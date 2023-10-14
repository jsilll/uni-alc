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
    
    # ctrl_c (bool) enable interrupts from ctrl-c (default: true)
    # dump_benchmarks (bool) dump benchmarks for profiling (default: false)
    # dump_models (bool) display intermediary models to stdout (default: false)
    # elim_01 (bool) eliminate 01 variables (default: true)
    # enable_sat (bool) enable the new SAT core for propositional constraints (default: true)
    # lns_conflicts (unsigned int) initial conflict count for LNS search (default: 1000)
    # maxlex.enable (bool) enable maxlex heuristic for lexicographic MaxSAT problems (default: true)
    # maxres.max_core_size (unsigned int) break batch of generated cores if size reaches this number (default: 3)
    # maxres.max_correction_set_size (unsigned int) allow generating correction set constraints up to maximal size (default: 3)
    # maxres.max_num_cores (unsigned int) maximal number of cores per round (default: 200)
    # maxres.pivot_on_correction_set (bool) reduce soft constraints if the current correction set is smaller than current core (default: true)
    # pp.wcnf (bool) print maxsat benchmark into wcnf format (default: false)
    # priority (symbol) select how to priortize objectives: 'lex' (lexicographic), 'pareto', 'box' (default: lex)
    # rlimit (unsigned int) resource limit (0 means no limit) (default: 0)
    # solution_prefix (symbol) path prefix to dump intermediary, but non-optimal, solutions (default: )
    # timeout (unsigned int) timeout (in milliseconds) (UINT_MAX and 0 mean no timeout) (default: 4294967295)
    # rc2.totalizer (bool) use totalizer for rc2 encoding (default: true)
    # incremental (bool) set incremental mode. It disables pre-processing and enables adding constraints in model event handler (default: false)
    # maxres.hill_climb (bool) give preference for large weight cores (default: true)

    # enable_core_rotate (bool) enable core rotation to both sample cores and correction sets (default: false)
    s.set("enable_core_rotate", True)
    # enable_lns (bool) enable LNS during weighted maxsat (default: false)
    s.set("enable_lns", True)
    # enable_sls (bool) enable SLS tuning during weighted maxsat (default: false)
    s.set("enable_sls", True)
    # maxres.add_upper_bound_block (bool) restict upper bound with constraint (default: false)
    s.set("maxres.add_upper_bound_block", True)
    # maxres.maximize_assignment (bool) find an MSS/MCS to improve current assignment (default: false)
    s.set("maxres.maximize_assignment", True)
    # maxres.wmax (bool) use weighted theory solver to constrain upper bounds (default: false)
    s.set("maxres.wmax", True)
    # maxsat_engine (symbol) select engine for maxsat: 'core_maxsat', 'wmax', 'maxres', 'pd-maxres', 'maxres-bin', 'rc2' (default: maxres)
    s.set("maxsat_engine", "maxres")
    # optsmt_engine (symbol) select optimization engine: 'basic', 'symba' (default: basic)
    s.set("optsmt_engine", "symba")
    # pb.compile_equality (bool) compile arithmetical equalities into pseudo-Boolean equality (instead of two inequalites) (default: false)
    s.set("pb.compile_equality", True)
    # pp.neat (bool) use neat (as opposed to less readable, but faster) pretty printer when displaying context (default: true)
    s.set("pp.neat", False)

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
    
    print(len(s.sexpr()), file=sys.stderr)

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
