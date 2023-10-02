#!/usr/bin/env python3

from typing import TextIO

from pysat.examples.rc2 import RC2
from pysat.formula import WCNF, IDPool
from pysat.pb import PBEnc, EncType as PBEncType
from pysat.card import CardEnc, EncType as CardEncType


def parse(file: TextIO):
    N = int(file.readline().strip())
    if N <= 1:
        raise ValueError("Number of groups of rules must be greater than 1")
    M = int(file.readline().strip())
    if M < 1:
        raise ValueError("Number of switches must be positive")
    required = list(map(int, file.readline().split()))
    stages = list(map(int, file.readline().split()))
    capacity = list(map(int, file.readline().split()))
    D = int(file.readline().strip())
    if D < 0:
        raise ValueError("Number of groups of rules must be positive")
    dependencies = list()
    for _ in range(D):
        i, j = map(int, file.readline().split())
        dependencies.append((i - 1, j - 1))
    return required, stages, capacity, dependencies


def solve(required, stages, capacities, dependencies):
    N_SWITCHES = len(stages)
    N_GROUPS = len(required)

    vpool = IDPool()
    solver = RC2(WCNF(), solver='g3')

    sw = [
        [
            vpool.id("Switch {} in position {}".format(i + 1, j + 1))
            for j in range(N_SWITCHES)
        ]
        for i in range(N_SWITCHES)
    ]
    gr = [
        [
            [
                vpool.id(
                    "Switch {} in stage {} has group {}".format(i + 1, j + 1, k + 1)
                )
                for k in range(N_GROUPS)
            ]
            for j in range(stages[i])
        ]
        for i in range(N_SWITCHES)
    ]
    besw = [
        [
            vpool.id("Switch {} is behind switch {}".format(i + 1, j + 1))
            for j in range(N_SWITCHES)
        ]
        for i in range(N_SWITCHES)
    ]
    begr = [
        [
            vpool.id("Group {} is behind group {}".format(i + 1, j + 1))
            for j in range(N_GROUPS)
        ]
        for i in range(N_GROUPS)
    ]

    # Relation sw <-> besw
    for s1 in range(N_SWITCHES):
        for s2 in range(N_SWITCHES):
            if s1 == s2:
                continue
            else:
                for p1 in range(N_SWITCHES):
                    for p2 in range(p1 + 1, N_SWITCHES):
                        solver.add_clause([-sw[s1][p1], -sw[s2][p2], besw[s1][s2]])
    # Relation gr <-> begr
    for g1 in range(N_GROUPS):
        for g2 in range(N_GROUPS):
            if g1 == g2:
                continue
            else:
                for s in range(N_SWITCHES):
                    for st1 in range(stages[s]):
                        for st2 in range(st1, stages[s]):
                            solver.add_clause(
                                [-gr[s][st1][g1], -gr[s][st2][g2], begr[g1][g2]]
                            )
    # Each switch is in exactly one position
    for lits in sw:
        for clause in CardEnc.equals(lits, vpool=vpool, encoding=CardEncType.seqcounter).clauses:
            solver.add_clause(clause)
    # Only one switch per position
    for pos in range(N_SWITCHES):
        for s1 in range(N_SWITCHES):
            for s2 in range(s1 + 1, N_SWITCHES):
                solver.add_clause([-sw[s1][pos], -sw[s2][pos]])
    # Each group is in exactly one stage out of all switches
    for group in range(N_GROUPS):
        lits = [gr[i][j][group] for i in range(N_SWITCHES) for j in range(stages[i])]
        for clause in CardEnc.equals(lits, vpool=vpool, encoding=CardEncType.seqcounter).clauses:
            solver.add_clause(clause)
    # The memory capacity of each switch stage is not exceeded
    for switch in range(N_SWITCHES):
        for stage in range(stages[switch]):
            weights = [required[group] for group in range(N_GROUPS)]
            lits = [gr[switch][stage][group] for group in range(N_GROUPS)]
            for clause in PBEnc.atmost(lits, weights, capacities[switch], vpool=vpool, encoding=PBEncType.bdd).clauses:
                solver.add_clause(clause)
    # For each dependency (i, j), then group j cannot be placed into a switch before the switch where group i is placed
    for g1, g2 in dependencies:
        for s1 in range(N_SWITCHES):
            for s2 in range(s1 + 1, N_SWITCHES):
                for st1 in range(stages[s1]):
                    for st2 in range(stages[s2]):
                        solver.add_clause(
                            # (g1, g2) => s1 is behind s2 /\ g1 in s2 => g2 not in s1
                            [-besw[s1][s2], -gr[s2][st2][g1], -gr[s1][st1][g2]]
                        )
                        solver.add_clause(
                            # (g1, g2) => s2 is behind s1 /\ g1 in s1 => g2 not in s2
                            [-besw[s2][s1], -gr[s1][st1][g1], -gr[s2][st2][g2]]
                        )
    # Minimize the overall number of re-circulations
    for g1, g2 in dependencies:
        solver.add_clause([-begr[g2][g1]], weight=1)

    model = solver.compute()

    if model is None:
        return -1, [], []

    # TODO: Remove
    # for i in range(1, vpool.top):
    #     obj = vpool.obj(i)
    #     if obj is not None:
    #         if model[i - 1] > 0:
    #             print(f"{obj} = {model[i - 1]}")
    #         else:
    #             print(f"{obj} = {model[i - 1]} (negated)")
    # print(list(map(lambda x: (x[0] + 1, x[1] + 1), dependencies)))
    # print(capacities)
    # print(required)

    switches = [0] * N_SWITCHES
    for s1 in range(N_SWITCHES):
        for s2 in range(N_SWITCHES):
            if model[sw[s1][s2] - 1] > 0:
                switches[s2] = s1 + 1
                break
    all_groups = list()
    for s1 in range(N_SWITCHES):
        groups = list()
        for st in range(stages[s1]):
            stage_groups = list()
            for g in range(N_GROUPS):
                if model[gr[s1][st][g] - 1] > 0:
                    stage_groups.append(g + 1)
            groups.append(stage_groups)
        all_groups.append(groups)

    return solver.cost, switches, all_groups


def output(file: TextIO, cost, switches, groups):
    if cost == -1:
        file.write("No solution\n")
    else:
        file.write(f"{cost}\n")
        file.write(" ".join(map(str, switches)) + " \n")
        for group in groups:
            file.write(", ".join(map(lambda g: " ".join(map(str, g)), group)))
            file.write("\n")


if __name__ == "__main__":
    import sys

    try:
        output(sys.stdout, *solve(*parse(sys.stdin)))
    except ValueError as e:
        sys.stderr.write(f"Error: {e}\n")
        sys.exit(1)
