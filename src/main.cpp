#include <parse.hpp>

#include <minisat/core/Solver.h>

void CardEnc(Minisat::Solver solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge){
  using Minisat::mkLit;
  std::vector<Minisat::Var> auxilary_vars(lits.size());

  std::cout << k << ge << std::endl;

  for (std::size_t i = 0; i < lits.size(); ++i) {
    auxilary_vars[i] = solver.newVar();
  }

  solver.addClause(~mkLit(lits[0]),~mkLit(auxilary_vars[0]));

  for (std::size_t i = 1; i < lits.size(); ++i) {
    solver.addClause(~mkLit(lits[i]),~mkLit(auxilary_vars[i])); // ~xi v ~Si 1,..,n 
    solver.addClause(~mkLit(auxilary_vars[i-1]),mkLit(auxilary_vars[i])); // ~Si-1 v Si 1,..,n
    
  
  }
  for(std::size_t i = 0; i < lits.size()-1; ++i){
    solver.addClause(~mkLit(lits[i]),mkLit(auxilary_vars[i-1])); // ~xi-1 v Si-1 1,..,n-1
  }

  std::cout << solver.toString() ; 
}

void Solve(const apr::Input &in) {
  std::int32_t n_switches = in.stages.size();
  std::int32_t n_groups = in.required.size();

  // sw[i][j] = switch i in position j
  std::vector<std::vector<Minisat::Var>> sw(
      n_switches, std::vector<Minisat::Var>(n_switches));

  // groups[i][j][k] = switch i in stage j has group k
  std::vector<std::vector<std::vector<Minisat::Var>>> gr(n_switches);
  for (std::int32_t i = 0; i < n_switches; ++i) {
    gr[i].resize(in.stages[i]);
    for (auto &stage : gr[i]) {
      stage.resize(n_groups);
    }
  }

  Minisat::Solver solver;
  for (std::int32_t i = 0; i < n_switches; ++i) {
    for (std::int32_t j = 0; j < n_switches; ++j) {
      sw[i][j] = solver.newVar();
    }
  }
  for (std::int32_t i = 0; i < n_switches; ++i) {
    for (std::int32_t j = 0; j < in.stages[i]; ++j) {
      for (std::int32_t k = 0; k < n_groups; ++k) {
        gr[i][j][k] = solver.newVar();
      }
    }
  }

  // TODO: cardinality constraint
  // each switch can only be in one position (=1)
  // CardEnc(solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge)
  // CardEnc(solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge)

  // TODO: cardinality constraint
  // each group of rules can only be placed once (=1)
  // CardEnc(solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge)
  // CardEnc(solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge)

  // The memory requirements of all groups of rules in each stage of the switch
  // is not higher than its capacity;
  // TODO: cardinality constraint (sum of groups in each stage <= capacity)
  // a + a + a + a + a + b + b + b + c + c <= k
  // CardEnc(solver, std::vector<Minisat::Var> &lits, std::int32_t k, bool ge)

  // For each (i, j) ∈ D, then group j cannot be placed into a switch that
  // occurs before the switch where group i is placed (i.e., there is no
  // re-circulation between switches);

  // The overall number of re-circulations is minimized. (optimalization)
  // cardinality constraint
}

int main(void) {
  apr::Input in;

  try {
    in = apr::Parse(std::cin);
  } catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
  }

  Solve(in);

  // TODO: print

  return EXIT_SUCCESS;
}
