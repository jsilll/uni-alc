#!/usr/bin/env python3

from typing import TextIO

from pysat.card import CardEnc
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF, IDPool

class Input:
    def __init__(self) -> None:
        # List of size N
        # N is the number of groups of rules
        self.required: list[int] = list()
        # List of size M
        # M is the number of switches
        self.stages: list[int] = list()
        # List of size M
        # M is the number of switches
        self.capacity: list[int] = list()
        # List of size D
        # D is the number of dependencies
        self.dependencies: list[tuple[int, int]] = list()

def parse(file: TextIO) -> Input:
    N = int(file.readline().strip())
    if N <= 1:
        raise ValueError("Number of groups of rules must be greater than 1")

    M = int(file.readline().strip())
    if M < 1:
        raise ValueError("Number of switches must be positive")

    inp = Input()

    inp.required = list(map(int, file.readline().split()))
    inp.stages = list(map(int, file.readline().split()))
    inp.capacity = list(map(int, file.readline().split()))

    D = int(file.readline().strip())
    if D < 0:
        raise ValueError("Number of groups of rules must be positive")

    for _ in range(D):
        i, j = map(int, file.readline().split())
        inp.dependencies.append((i - 1, j - 1))

    return inp

class Solution:
    def __init__(self) -> None:
        # Number of re-circulations
        self.cost: int = 0
        # Switch order
        self.switches: list[int] = list()
        # Group order for each switch
        self.groups: list[list[list[int]]] = list()

def solve(input: Input):
    # Number of switches
    M = len(input.stages)
    # Number of groups of rules
    N = len(input.required)

    # -- Variable Pool --
    vpool = IDPool()

    # -- Variables --
    SW = "Switch {} in position {}"
    sw = [[vpool.id(SW.format(i + 1, j + 1)) for j in range(M)] for i in range(M)]

    GR = "Switch {} in stage {} has group {}"
    gr = [
        [
            [vpool.id(GR.format(i + 1, j + 1, k + 1)) for k in range(N)]
            for j in range(input.stages[i])
        ]
        for i in range(M)
    ]

    BESW = "Switch {} is behind switch {}"
    besw = [[vpool.id(BESW.format(i + 1, j + 1)) for j in range(M)] for i in range(M)]

    BEGR = "Group {} is behind group {}"
    begr = [[vpool.id(BEGR.format(i + 1, j + 1)) for j in range(N)] for i in range(N)]

    # -- Solver --
    solver = RC2(WCNF())

    # -- Consistency --
    # SW and GRSW relation
    for s1 in range(M):
        for s2 in range(M):
            if s1 == s2:
                solver.add_clause([-besw[s1][s2]])
            else:
                for p1 in range(M):
                    for p2 in range(p1 + 1, M):
                        solver.add_clause([-sw[s1][p1], -sw[s2][p2], besw[p1][p2]])
    # GR and BEGR relation
    for g1 in range(N):
        for g2 in range(N):
            if g1 == g2:
                solver.add_clause([-begr[g1][g2]])
            else:
                for s in range(M):
                    for st1 in range(input.stages[s]):
                        for st2 in range(st1, input.stages[s]):
                            solver.add_clause(
                                [-gr[s][st1][g1], -gr[s][st2][g2], begr[g1][g2]]
                            )

    # -- Constraints --
    # Each switch can only be in one position (=1)
    for lits in sw:
        for clause in CardEnc.equals(lits, 1, vpool=vpool).clauses:
            solver.add_clause(clause)
    # Each group of rules can only be placed once (=1)
    for group in range(N):
        lits = [gr[i][j][group] for i in range(M) for j in range(input.stages[i])]
        print("CardEnc for group {} with lits {}".format(group, lits))
        for clause in CardEnc.equals(lits, 1, vpool=vpool).clauses:
            solver.add_clause(clause)
    # The memory requirements of all groups of rules in
    # each stage of the switch is not higher than its capacity;
    for switch in range(M):
        for stage in range(input.stages[switch]):
            lits = sum(
                [
                    [gr[switch][stage][group]] * input.required[group]
                    for group in range(N)
                ],
                [],
            )
            for clause in CardEnc.atmost(
                lits, input.capacity[switch], vpool=vpool
            ).clauses:
                solver.add_clause(clause)
    # For each (i, j) in D, then group j cannot be placed into a
    # switch that occurs before the switch where group i is placed
    for g1, g2 in input.dependencies:
        for s1 in range(M):
            for s2 in range(s1):
                for j1 in range(input.stages[s1]):
                    for j2 in range(input.stages[s2]):
                        solver.add_clause(
                            [-besw[s1][s2], -gr[s1][j1][g2], -gr[s2][j2][g1]]
                        )
    # For every dependency (g1, g2) in D if g1 is placed in the same
    # switch as g2 and g1 is placed in a stage before or equal
    # to g2's stage, then there's a re-circulation. Minimize the
    # overall number of re-circulations
    for g1, g2 in input.dependencies:
        solver.add_clause([-begr[g2][g1]], weight=1)

    # -- Solve --
    model = solver.compute()
    if model is None:
        return None

    # -- Debug --
    for var in range(1, vpool.top + 1):
        obj = vpool.obj(var)
        if obj != None:
            if model[var] > 0:
                print(obj)
            else:
                print(f"-{obj}")

    # -- Build Solution --
    solution = Solution()
    solution.cost = solver.cost
    # Switch order
    solution.switches = [0] * M
    for s in range(M):
        for p in range(M):
            if model[sw[s][p]] > 0:
                solution.switches[p] = s + 1
                break
    # Group order for each switch
    solution.groups = [[[]] * input.stages[s] for s in range(M)]
    for s in range(M):
        for st in range(input.stages[s]):
            for g in range(N):
                if model[gr[s][st][g]] > 0:
                    solution.groups[s][st].append(g + 1)
                    break

    return solution


def output(file: TextIO, solution: Solution) -> None:
    file.write(f"{solution.cost}\n")
    file.write(" ".join(map(str, solution.switches)))
    file.write("\n")
    for groups in solution.groups:
        file.write(", ".join(map(lambda g: " ".join(map(str, g)), groups)))
        file.write("\n")


if __name__ == "__main__":
    import sys

    try:
        solution = solve(parse(sys.stdin))
        if solution:
            output(sys.stdout, solution)
        else:
            print("No solution found", file=sys.stderr)
    except ValueError as e:
        print(e, file=sys.stderr)
        sys.exit(1)
