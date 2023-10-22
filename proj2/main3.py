#!/usr/bin/python3
# alc23 - 2 - project2
# DO NOT remove or edit the lines above. Thank you.

from z3 import *

from typing import TextIO
from collections import defaultdict
from itertools import accumulate, permutations


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


def toposort(edges: list[tuple[int, int]]) -> list[int]:
    def helper(u, graph, visited, res):
        visited[u] = True
        for v in graph[u]:
            if not visited[v]:
                helper(v, graph, visited, res)
        res.append(u)

    graph = defaultdict(list)
    for u, v in edges:
        graph[u].append(v)
        if v not in graph:
            graph[v] = []
    res = []
    visited = [False] * (len(graph))
    for i in reversed(range(len(graph))):
        if not visited[i]:
            helper(i, graph, visited, res)
    return res


def solve(required, stages, capacity, dependencies):
    N_STAGES = sum(stages)
    N_GROUPS = len(required)
    N_SWITCHES = len(stages)

    offset = [0] + list(accumulate(stages))[:-1]

    group_stage = [Int(f"Group {i+1} stage") for i in range(N_GROUPS)]
    group_switch = [Int(f"Group {i+1} switch") for i in range(N_GROUPS)]
    switch_behind = [
        [Bool(f"Switch {i+1} is behind switch {j + 1}") for j in range(N_SWITCHES)]
        for i in range(N_SWITCHES)
    ]

    stages_memory = [[Int(f'Group {gr} is in stage {st}') for gr in range(N_GROUPS)]
                      for st in range(N_STAGES)]

    s = Optimize()

    for s1 in range(N_SWITCHES):
        for s2 in range(s1 + 1, N_SWITCHES):
            s.add(switch_behind[s1][s2] == Not(switch_behind[s2][s1]))
            for s3 in range(s2 + 1, N_SWITCHES):
                for p in permutations([s1, s2, s3]):
                    s.add(
                        Implies(
                            And(switch_behind[p[0]][p[1]], switch_behind[p[1]][p[2]]),
                            switch_behind[p[0]][p[2]],
                        )
                    )

    for g1 in range(N_GROUPS):
        s.add(0 <= group_stage[g1])
        s.add(0 <= group_switch[g1])
        s.add(group_stage[g1] < N_STAGES)
        s.add(group_switch[g1] < N_SWITCHES)

    for s1, (n, o) in enumerate(zip(stages, offset)):
        for g1 in range(N_GROUPS):
            s.add(
                Implies(
                    group_switch[g1] == s1,
                    And(o <= group_stage[g1], group_stage[g1] < o + n),
                )
            )
        for st1 in range(o, o + n):
            for g1 in range(N_GROUPS):
                s.add(Implies(group_stage[g1] == st1, group_switch[g1] == s1))
                s.add(And(stages_memory[st1][g1] >= 0, stages_memory[st1][g1] <= 1))
                s.add(Implies(group_stage[g1] == st1, stages_memory[st1][g1] == 1))
            s.add(
                Sum(
                    [ stages_memory[st1][gr] * req for gr,req in zip(range(N_GROUPS), required)]
                )
                <= capacity[s1]
            )

    for g1, g2 in dependencies:
        s.add_soft(
            Implies(
                group_switch[g1] == group_switch[g2], group_stage[g1] < group_stage[g2]
            )
        )
        for s1 in range(N_SWITCHES):
            for s2 in range(s1 + 1, N_SWITCHES):
                for p in permutations([s1, s2]):
                    s.add(
                        Implies(
                            And(
                                group_switch[g1] == p[0],
                                group_switch[g2] == p[1],
                            ),
                            switch_behind[p[0]][p[1]],
                        )
                    )

    print(f"Finished Enconding: {len(s.sexpr())} constraints", file=sys.stderr)

    if s.check() == sat:
        print("Finished Solving: Satisfiable", file=sys.stderr)
        m = s.model()

        cost = sum([m.evaluate(o).as_long() for o in s.objectives()])
        switches = (
            list(
                map(
                    lambda x: x + 1,
                    toposort(
                        [
                            (j, i) if m.evaluate(switch_behind[i][j]) else (i, j)
                            for i in range(N_SWITCHES)
                            for j in range(i + 1, N_SWITCHES)
                            if i != j
                        ]
                    ),
                )
            )
            if N_SWITCHES > 1
            else [1]
        )

        groups = [[[] for _ in range(stages[j])] for j in range(N_SWITCHES)]
        for group, stage, switch in map(
            lambda x: (x[0], x[1] - offset[x[2]], x[2]),
            sorted(
                [
                    (
                        i,
                        m.evaluate(group_stage[i]).as_long(),
                        m.evaluate(group_switch[i]).as_long(),
                    )
                    for i in range(N_GROUPS)
                ],
                key=lambda x: (x[2], x[1]),
            ),
        ):
            groups[switch][stage].append(group + 1)

        print("Finished Decoding", file=sys.stderr)
        return cost, switches, groups

    print("Finished Solving: Unsatisfiable", file=sys.stderr)
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
    required, stages, capacities, dependencies = parse(sys.stdin)
    cost, switches, groups = solve(required, stages, capacities, dependencies)
    output(sys.stdout, cost, switches, groups)
