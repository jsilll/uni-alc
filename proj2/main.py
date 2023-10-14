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
    dependencies = list()
    for _ in range(D):
        i, j = map(int, file.readline().split())
        dependencies.append((i - 1, j - 1))
    return required, stages, capacity, dependencies


def solve(required, stages, capacities, dependencies):
    N_GROUPS = len(required)
    N_SWITCHES = len(stages)

    # Variables
    groups = [
        (Int(f"Group{i+1}'s switch"), Int(f"Group{i+1}'s stage "))
        for i in range(N_GROUPS)
    ]
    switches = [Int(f"Switch{i+1}'s position") for i in range(N_SWITCHES)]

    # Optimizer
    s = Optimize()
    
    # Optimizer settings
    s.set("timeout", 10000)
    s.set("maxsat_engine", "rc2")

    for i in range(N_SWITCHES):
        # Switches' position is valid
        s.add(switches[i] >= 0)
        s.add(switches[i] < N_SWITCHES)
    # Switches should be in distinct positions
    s.add(Distinct(switches))
    for i in range(N_GROUPS):
        # Group's switch and group are valid
        s.add(groups[i][0] >= 0)
        s.add(groups[i][1] >= 0)
        s.add(groups[i][0] < N_SWITCHES)
        for switch in range(N_SWITCHES):
            # Group's stage must be valid
            s.add(Implies(groups[i][0] == switch, groups[i][1] < stages[switch]))
    for switch in range(N_SWITCHES):
        for stage in range(stages[switch]):
            # Each stage's capacity requirements should be met
            s.add(
                Sum(
                    [
                        If(
                            And(groups[i][0] == switch, groups[i][1] == stage),
                            required[i],
                            0,
                        )
                        for i in range(N_GROUPS)
                    ]
                )
                <= capacities[switch]
            )
    for g1, g2 in dependencies:
        for s1 in range(N_SWITCHES):
            for s2 in range(s1 + 1, N_SWITCHES):
                # There's no re-circulations between switches
                s.add(
                    Implies(
                        And(groups[g1][0] == s1, groups[g2][0] == s2),
                        switches[s1] <= switches[s2],
                    )
                )
                s.add(
                    Implies(
                        And(groups[g1][0] == s2, groups[g2][0] == s1),
                        switches[s2] <= switches[s1],
                    )
                )
    # Transform this into soft constraints
    for g1, g2 in dependencies:
        s.add_soft(Implies(groups[g1][0] == groups[g2][0], groups[g1][1] < groups[g2][1]))

    if not s.check() == sat:
        return -1, [], []
    else:
        m = s.model()

        cost = sum([m.evaluate(o).as_long() for o in s.objectives()])

        sw = [0] * N_SWITCHES
        for i in range(N_SWITCHES):
            sw[m[switches[i]].as_long()] = i + 1

        gp = [[[] for _ in range(stages[j])] for j in range(N_SWITCHES)]
        for group, (switch, stage) in enumerate(groups):
            gp[m[switch].as_long()][m[stage].as_long()].append(group + 1)

        return cost, sw, gp


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
