 from collections import defaultdict

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
    res = []
    visited = [False] * (len(graph) + 1)
    for i in reversed(range(len(graph))):
        if not visited[i]:
            helper(i, graph, visited, res)
    return res