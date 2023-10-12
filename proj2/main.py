#!/usr/bin/python3
# alc23 - 2 - project1 
# DO NOT remove or edit the lines above. Thank you.

from typing import TextIO

from z3 import *


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
    s = Optimize()
    sws = [Int(f"SW {i+1} is in position") for i in range(N_SWITCHES)]

    # groups[i][0] -> group's switch
    # groups[i][1] -> group's stage
    groups = [(Int(f"Group {i+1} is in switch"), Int(f"Group {i+1} is in stage ")) for i in range(N_GROUPS)]

    # Each switch is in a single postion
    for i in range(N_SWITCHES):
        s.add(And(sws[i] >= 0, sws[i] < N_SWITCHES))

    # All switches are in different positions
    s.add(Distinct(sws))

    # Each group is in a single position
    for i in range(N_GROUPS):
        s.add(And(groups[i][0] >= 0, groups[i][0] < N_SWITCHES))

        for switch in range(N_SWITCHES):
            s.add(And(groups[i][1] >= 0, \
                                If(groups[i][0] == switch, groups[i][1] < stages[switch],True)))

    # capacity constrains
    for switch in range(N_SWITCHES):
        for stage in range(stages[switch]):
            s.add(Sum([If(And(groups[i][0] == switch, groups[i][1] == stage), \
                                      required[i], 0) for i in range(N_GROUPS)]) <= capacities[switch])

    # For each dependency (i, j), group i must be in a switch lower or equal than group j
    for g1,g2 in dependencies:
        s.add(groups[g1][0] <= groups[g2][0])

    # Minimize recirculations
    cost = Int("cost")
    s.add(cost == Sum([If(And( groups[g1][0] == groups[g2][0],
                              groups[g1][1] >= groups[g2][1]), 1, 0) for g1,g2 in dependencies]))
    s.minimize(cost)

    if s.check() == sat:
        model = s.model()
        cost = model[cost].as_long()
        sw = [0 for i in range(N_SWITCHES)]

        for i in range(N_SWITCHES):
            sw[model[sws[i]].as_long()] = i+1
        
        gp =  [[[] for i in range(stages[j])] for j in range(N_SWITCHES)]
        for group,tup in enumerate(groups):
            switch,stage = tup
            gp[model[switch].as_long()][model[stage].as_long()].append(group+1)
            
        return cost, sw, gp
    else:
        return -1, [], []


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
