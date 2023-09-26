#!/usr/bin/env python3

from typing import TextIO

from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Glucose3

class Input:
    def __init__(self) -> None:
        # List of size N, where N is the number of groups of rules
        self.required : list[int] = list()
        # List of size M, where M is the number of switches
        self.stages : list[int] = list()
        # List of size M, where M is the number of switches
        self.capacity : list[int] = list()
        # List of size D, where D is the number of dependencies
        self.dependencies : list[tuple[int, int]] = list()
        
    def __repr__(self) -> str:
        return self.__str__()

    def __str__(self) -> str:
        return f"Required: {self.required}\nStages: {self.stages}\nCapacity: {self.capacity}\nDependencies: {self.dependencies}"

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

def solve(input:Input):
    # Number of switches
    M = len(input.stages)
    # Number of groups of rules
    N = len(input.required)
    # Variable Pool
    vpool = IDPool()

    # -- Variables --
    SW='Switch {} in position {}'
    sw = [[vpool.id(SW.format(i + 1, j + 1)) for j in range(M)]for i in range(M)]
    GR='Switch {} in stage {} has group {}' 
    gr = [[[vpool.id(GR.format(i + 1, j + 1, k + 1)) for k in range(N)] for j in range(input.stages[i])] for i in range(M)]
    # be[i][j] = switch i is behind switch j
    BE='Switch {} is behind switch {}'
    be = [[vpool.id(BE.format(i + 1, j + 1)) for j in range(M)] for i in range(M)]

    # -- Debug --
    # for lits in sw:
    #     for lit in lits:
    #         print(vpool.obj(lit))
    # for litss in gr:
    #     for lits in litss:
    #         for lit in lits:
    #             print(vpool.obj(lit))
    # for lits in be:
    #     for lit in lits:
    #         print(vpool.obj(lit))

    # -- Clauses --
    solver = Glucose3()

    # -- Consistency --
    # sw and be consistency
    for s1 in range(M):
        for s2 in range(M):
            if s1 == s2:
                solver.add_clause([-be[s1][s2]])
            else:
                for p1 in range(M):
                    for p2 in range(p1 + 1, M):
                        solver.add_clause([-sw[s1][p1], -sw[s2][p2], be[p1][p2]])

    # -- Constraints --
    # Each switch can only be in one position (=1)
    for lits in sw:
        for clause in CardEnc.equals(lits, 1, vpool=vpool).clauses:
            solver.add_clause(clause)
    # Each group of rules can only be placed once (=1)
    for group in range(N):
        lits = [gr[i][j][group] for i in range(M) for j in range(input.stages[i])]
        for clause in CardEnc.equals(lits, 1, vpool=vpool).clauses:
            solver.add_clause(clause)
    # The memory requirements of all groups of rules in each stage of the switch is not higher than its capacity;
    for switch in range(M):
        for stage in range(input.stages[switch]):
            lits = sum([[gr[switch][stage][group]] * input.required[group] for group in range(N)], [])
            for clause in CardEnc.atmost(lits, input.capacity[switch], vpool=vpool).clauses:
                solver.add_clause(clause)
    # For each (i, j) ∈ D, then group j cannot be placed into a switch that occurs before the switch where group i is placed
    for g1, g2 in input.dependencies:
        for s1 in range(M):
            for s2 in range(s1):
                for j1 in range(input.stages[s1]):
                    for j2 in range(input.stages[s2]):
                        solver.add_clause([-be[s1][s2], -gr[s1][j1][g2], -gr[s2][j2][g1]])
    # The overall number of re-circulations is minimized
    # for every dependency (g1, g2) ∈ D
    # if g1 is placed in the same switch as g2, then if g1 is placed in a stage before or equal
    # to g2's, then there's a re-circulation (soft constraint)
    # TODO: Implement

    # -- Solve --
    return vpool, solver.solve(), solver.get_model()

def output(file: TextIO, model) -> None:
    for lit in model:
        if lit >= 0:
            print(f"{vpool.obj(lit) if vpool.obj(lit) else lit}", file=file)
        else:
            print(f"-{vpool.obj(abs(lit)) if vpool.obj(abs(lit)) else abs(lit)}", file=file)

if __name__ == "__main__":
    import sys
    try:
        vpool, solution, model = solve(parse(sys.stdin))
        if solution:
            output(sys.stdout, model)
    except ValueError as e:
        print(e)
        sys.exit(1)