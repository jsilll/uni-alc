#!/usr/bin/env python3
import sys
from pysat.solvers import Glucose3
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc, EncType
from typing import TextIO

SW='SW[{}][{}]'
GR='GR[{}][{}][{}]'

class Input:
    def __init__(self) -> None:
        self.required = [] # n - number of groups
        self.stages = [] #  m - number of switches
        self.capacity = [] # m 
        self.dependencies = [] # d - number of dependencies

def parse(text: TextIO) -> Input:
    n = int(text.readline().strip())
    if n <= 1:
        raise ValueError("Number of groups of rules must be greater than 1")

    m = int(text.readline().strip())
    if m < 1:
        raise ValueError("Number of switches must be positive")

    inp = Input()

    inp.required = list(map(int, text.readline().split()))
    inp.stages = list(map(int, text.readline().split()))
    inp.capacity = list(map(int, text.readline().split()))

    d = int(text.readline().strip())
    if d < 0:
        raise ValueError("Number of groups of rules must be positive")

    for _ in range(d):
        i, j = map(int, text.readline().split())
        inp.dependencies.append((i, j))

    return inp
    
def solve(input:Input) -> None:

    vpool = IDPool()
    solver = Glucose3(vpool=vpool)
    n_switches = len(input.stages)
    n_groups = len(input.required)

    # sw[i][j] = switch i in position j
    sw = [[None] * n_switches for _ in range(n_switches)]

    # groups[i][j][k] = switch i in stage j has group k
    gr = [[[None] * n_groups for _ in range(input.stages[i])] for i in range(n_switches)]

    # Initialize variables
    for i in range(n_switches):
        for j in range(n_switches):
            sw[i][j] = vpool.id(SW.format(i, j))


    for i in range(n_switches):
        for j in range(input.stages[i]):
            for k in range(n_groups):
                gr[i][j][k] = vpool.id(GR.format(i, j, k))

    # each switch can only be in one position (=1)
    for switch in sw:
        enc = CardEnc.equals(switch, 1, vpool=vpool)

        for clause in enc.clauses:
            solver.add_clause(clause)

    ## each group of rules can only be placed once (=1)
    for group in n_groups:
        lits = [ gr[i][j][group] for i in range(n_switches) for j in range(input.stages[i]) ]
        enc = CardEnc.equals(lits, 1, vpool=vpool)

        for clause in enc.clauses:
            solver.add_clause(clause)


  ## The memory requirements of all groups of rules in each stage of the switch
  ## is not higher than its capacity;
  ## TODO: cardinality constraint (sum of groups in each stage <= capacity)

    for switch in range(n_switches):
        for stage in range(input.stages[switch]):
            lits = [ [gr[switch][stage][group]] * input.required[group] \
                     for group in range(n_groups) ]
            enc = CardEnc.atmost(lits, input.capacity[switch], vpool=vpool)

            for clause in enc.clauses:
                solver.add_clause(clause)
  ## a + a + a + a + a + b + b + b + c + c <= k
  ## CardEnc(solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge)
  

  ## For each (i, j) ∈ D, then group j cannot be placed into a switch that
  ## occurs before the switch where group i is placed (i.e., there is no
  ## re-circulation between switches);

  ## The overall number of re-circulations is minimized. (optimalization)
  ## cardinality constraint
    
if __name__ == "__main__":
    try:
        solve(parse(sys.stdin))
    except ValueError as e:
        print(e)
        sys.exit(1)