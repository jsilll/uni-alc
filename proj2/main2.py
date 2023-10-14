#!/usr/bin/python3
# alc23 - 2 - project1
# DO NOT remove or edit the lines above. Thank you.

from z3 import *
from typing import TextIO


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

    dependencies = list(
        map(lambda x: tuple(map(lambda y: int(y) - 1, x.split())), file.readlines())
    )

    return required, stages, capacity, dependencies


def solve(required, stages, capacities, dependencies):
    N_GROUPS = len(required)
    N_SWITCHES = len(stages)

    switches = [Int(f"Switch{i+1}'s position") for i in range(N_SWITCHES)]
    groups = [
        (Int(f"Group{i+1}'s position"), Int(f"Group{i+1}'s stage "))
        for i in range(N_GROUPS)
    ]

    s = Optimize()

    s.add(Distinct(switches))

    for i in range(N_GROUPS):
        s.add(groups[i][0] >= 0)
        s.add(groups[i][1] >= 0)
        s.add(groups[i][0] < N_SWITCHES)
        for j in range(N_SWITCHES):
            s.add(Implies(groups[i][0] == switches[j], groups[i][1] < stages[j]))

    for i in range(N_SWITCHES):
        s.add(switches[i] >= 0)
        s.add(switches[i] < N_SWITCHES)
        for j in range(stages[i]):
            s.add(
                Sum(
                    [
                        If(
                            And(groups[k][0] == switches[i], groups[k][1] == j),
                            required[k],
                            0,
                        )
                        for k in range(N_GROUPS)
                    ]
                )
                <= capacities[i]
            )

    for g1, g2 in dependencies:
        s.add(groups[g1][0] <= groups[g2][0])
        s.add_soft(
            Implies(groups[g1][0] == groups[g2][0], groups[g1][1] < groups[g2][1])
        )

    s.set("maxres.wmax", True)
    s.set("maxsat_engine", "maxres")
    s.set("maxres.maximize_assignment", True)
    s.set("maxres.add_upper_bound_block", True)
    s.set("enable_lns", True)
    s.set("enable_sls", True)
    s.set("enable_core_rotate", True)
    s.set("pp.neat", False)
    s.set("optsmt_engine", "symba")
    s.set("pb.compile_equality", True)
    
    print(len(s.sexpr()), file=sys.stderr)

    if s.check() == sat:
        m = s.model()

        cost = sum([m.evaluate(o).as_long() for o in s.objectives()])

        sw = [0] * N_SWITCHES
        for i in range(N_SWITCHES):
            s = m.evaluate(switches[i]).as_long()
            sw[s] = i + 1

        gp = [[[] for _ in range(stages[j])] for j in range(N_SWITCHES)]
        for group, (pos, stage) in enumerate(groups):
            switch = sw[m.evaluate(pos).as_long()] - 1
            gp[switch][m.evaluate(stage).as_long()].append(group + 1)

        return cost, sw, gp

    else:
        return -1, [], []


def output(file: TextIO, cost, switches, groups):
    if cost == -1:
        file.write("No solution")
    else:
        file.write(f"{cost}\n")
        file.write(" ".join(map(str, switches)) + " \n")
        for group in groups:
            file.write(", ".join(map(lambda g: " ".join(map(str, g)), group)))
            file.write("\n")


if __name__ == "__main__":
    import sys

    required, stages, capacities, dependencies = parse(sys.stdin)
    cost, switches, groups = solve(required, stages, capacities, dependencies)
    output(sys.stdout, cost, switches, groups)
