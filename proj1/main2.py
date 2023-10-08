#!/usr/bin/python3
# alc23 - 2 - project1
# DO NOT remove or edit the lines above. Thank you.

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
    MAX_STAGES = max(stages)

    vpool = IDPool()
    solver = RC2(WCNF(), solver="g3")

    # 1st Order Variables
    swpos = [
        [
            vpool.id("Switch {} in position {}".format(i + 1, j + 1))
            for j in range(N_SWITCHES)
        ]
        for i in range(N_SWITCHES)
    ]
    swgr = [
        [
            vpool.id("Switch {} has group {}".format(i + 1, j + 1))
            for j in range(N_GROUPS)
        ]
        for i in range(N_SWITCHES)
    ]
    grst = [
        [
            vpool.id("Group {} is in stage {}".format(i + 1, j + 1))
            for j in range(MAX_STAGES)
        ]
        for i in range(N_GROUPS)
    ]

    # 2nd Order Variables
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

    # Relation swpos <-> besw
    for switch in range(N_SWITCHES):
        for pos in range(switch + 1, N_SWITCHES):
            for p1 in range(N_SWITCHES):
                for p2 in range(p1 + 1, N_SWITCHES):
                    solver.add_clause([-swpos[switch][p1], -swpos[pos][p2], besw[switch][pos]])
                    solver.add_clause([-swpos[switch][p2], -swpos[pos][p1], besw[pos][switch]])
    # Relation (besw + swgr) <-> begr and (swgr + grst) <-> begr
    for g1 in range(N_GROUPS):
        for g2 in range(g1 + 1, N_GROUPS):
            for switch in range(N_SWITCHES):
                for pos in range(switch + 1, N_SWITCHES):
                    solver.add_clause(
                        [-besw[switch][pos], -swgr[switch][g1], -swgr[pos][g2], begr[g1][g2]]
                    )
                    solver.add_clause(
                        [-besw[pos][switch], -swgr[pos][g1], -swgr[switch][g2], begr[g1][g2]]
                    )
                    solver.add_clause(
                        [-besw[switch][pos], -swgr[switch][g2], -swgr[pos][g1], begr[g2][g1]]
                    )
                    solver.add_clause(
                        [-besw[pos][switch], -swgr[pos][g2], -swgr[switch][g1], begr[g2][g1]]
                    )
                for st1 in range(stages[switch]):
                    solver.add_clause(
                        [
                            -swgr[switch][g1],
                            -swgr[switch][g2],
                            -grst[g1][st1],
                            -grst[g2][st1],
                            begr[g1][g2],
                        ]
                    )
                    for st2 in range(st1 + 1, stages[switch]):
                        solver.add_clause(
                            [
                                -swgr[switch][g1],
                                -swgr[switch][g2],
                                -grst[g1][st1],
                                -grst[g2][st2],
                                begr[g1][g2],
                            ]
                        )
                        solver.add_clause(
                            [
                                -swgr[switch][g1],
                                -swgr[switch][g2],
                                -grst[g1][st2],
                                -grst[g2][st1],
                                begr[g2][g1],
                            ]
                        )
    # Each switch is in exactly one position
    for lits in swpos:
        for clause in CardEnc.equals(lits, bound=1, vpool=vpool, encoding=CardEncType.seqcounter):
            solver.add_clause(clause)
    # Each position has at most one switch
    for pos in range(N_SWITCHES):
        lits = [swpos[switch][pos] for switch in range(N_SWITCHES)]
        for clause in CardEnc.atmost(lits, bound=1, vpool=vpool, encoding=CardEncType.seqcounter):
            solver.add_clause(clause)
    # Each group is in exactly one switch
    for group in range(N_GROUPS):
        lits = [swgr[switch][group] for switch in range(N_SWITCHES)]
        for clause in CardEnc.equals(lits, bound=1, vpool=vpool, encoding=CardEncType.seqcounter):
            solver.add_clause(clause)
    # Each group is in exactly one stage
    for group, lits in enumerate(grst):
        for switch in range(N_SWITCHES):
            for clause in CardEnc.equals(lits[:stages[switch]], bound=1, vpool=vpool, encoding=CardEncType.seqcounter):
                solver.add_clause([-swgr[switch][group]] + clause)
    # Each switch has enough capacity for its groups
    weights = [required[group] for group in groups[switch][stage]]
    for switch in range(N_SWITCHES):
        for stage in range(stages[switch]):
            lits = [grst[group][stage] for group in range(N_GROUPS)]
            for clause in PBEnc.atleast(lits, bound=capacities[switch], vpool=vpool, encoding=PBEncType.seqcounter):
                solver.add_clause(clause)
    # For each dependency (i, j), then group j cannot be placed into a switch before the switch where group i is placed
    for g1, g2 in dependencies:
        for switch in range(N_SWITCHES):
            for pos in range(switch + 1, N_SWITCHES):
                solver.add_clause(
                    # (g1, g2) => s1 is behind s2 /\ g1 in s2 => g2 not in s1
                    [-besw[switch][pos], -swgr[pos][g1], -swgr[switch][g2]]
                )
                solver.add_clause(
                    # (g1, g2) => s2 is behind s1 /\ g1 in s1 => g2 not in s2
                    [-besw[pos][switch], -swgr[switch][g1], -swgr[pos][g2]]
                )
    # Minimize the overall number of re-circulations
    for g1, g2 in dependencies:
        solver.add_clause([-begr[g2][g1]], weight=1)

    model = solver.compute()

    if model is None:
        return -1, [], []

    # Collect the ordering of switches into a list
    switches = [0] * N_SWITCHES
    for switch in range(N_SWITCHES):
        for pos in range(N_SWITCHES):
            if model[swpos[switch][pos] - 1] > 0:
                switches[pos] = switch + 1
                break

    groups = list()
    for switch in range(N_SWITCHES):
        switch_groups = list()
        for stage in range(stages[switch]):
            stage_groups = list()
            for group in range(N_GROUPS):
                if model[swgr[switch][group] - 1] > 0 and model[grst[group][stage] - 1] > 0:
                    stage_groups.append(group + 1)
            switch_groups.append(stage_groups)
        groups.append(switch_groups)

    return solver.cost, switches, groups

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