/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for CaDiCaL SAT Solver.
 *
 * Implementation of the CaDiCaL SAT solver for cvc5 (bit-vectors).
 */

#include "prop/cadical.h"

#include "base/check.h"
#include "prop/theory_proxy.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace prop {

/* CadicalSolver ------------------------------------------------------------ */

using CadicalLit = int;
using CadicalVar = int;

// helper functions
namespace {

SatValue toSatValue(int result)
{
  if (result == 10) return SAT_VALUE_TRUE;
  if (result == 20) return SAT_VALUE_FALSE;
  Assert(result == 0);
  return SAT_VALUE_UNKNOWN;
}

// Note: CaDiCaL returns lit/-lit for true/false. Older versions returned 1/-1.
SatValue toSatValueLit(int value)
{
  if (value > 0) return SAT_VALUE_TRUE;
  Assert(value < 0);
  return SAT_VALUE_FALSE;
}

CadicalLit toCadicalLit(const SatLiteral lit)
{
  return lit.isNegated() ? -lit.getSatVariable() : lit.getSatVariable();
}

CadicalVar toCadicalVar(SatVariable var) { return var; }

SatLiteral toSatLiteral(const CadicalLit lit)
{
  return lit < 0 ? SatLiteral(SatVariable(-lit), true)
                 : SatLiteral(SatVariable(lit), false);
}

}  // namespace helper functions

CadicalSolver::CadicalSolver(StatisticsRegistry& registry,
                             const std::string& name)
    : d_solver(new CaDiCaL::Solver()),
      // Note: CaDiCaL variables start with index 1 rather than 0 since negated
      //       literals are represented as the negation of the index.
      d_nextVarIdx(1),
      d_inSatMode(false),
      d_statistics(registry, name)
{
}

void CadicalSolver::init()
{
  d_true = newVar();
  d_false = newVar();

  d_solver->set("quiet", 1);  // CaDiCaL is verbose by default
  d_solver->add(toCadicalVar(d_true));
  d_solver->add(0);
  d_solver->add(-toCadicalVar(d_false));
  d_solver->add(0);
}

CadicalSolver::~CadicalSolver() {}

/**
 * Terminator class that notifies CaDiCaL to terminate when the resource limit
 * is reached (used for resource limits specified via --rlimit or --tlimit).
 */
class ResourceLimitTerminator : public CaDiCaL::Terminator
{
 public:
  ResourceLimitTerminator(ResourceManager& resmgr) : d_resmgr(resmgr){};

  bool terminate() override
  {
    d_resmgr.spendResource(Resource::BvSatStep);
    return d_resmgr.out();
  }

 private:
  ResourceManager& d_resmgr;
};

void CadicalSolver::setResourceLimit(ResourceManager* resmgr)
{
  d_terminator.reset(new ResourceLimitTerminator(*resmgr));
  d_solver->connect_terminator(d_terminator.get());
}

ClauseId CadicalSolver::addClause(SatClause& clause, bool removable)
{
  for (const SatLiteral& lit : clause)
  {
    d_solver->add(toCadicalLit(lit));
  }
  d_solver->add(0);
  ++d_statistics.d_numClauses;
  return ClauseIdError;
}

ClauseId CadicalSolver::addXorClause(SatClause& clause,
                                     bool rhs,
                                     bool removable)
{
  Unreachable() << "CaDiCaL does not support adding XOR clauses.";
}

SatVariable CadicalSolver::newVar(bool isTheoryAtom, bool canErase)
{
  ++d_statistics.d_numVariables;
  return d_nextVarIdx++;
}

SatVariable CadicalSolver::trueVar() { return d_true; }

SatVariable CadicalSolver::falseVar() { return d_false; }

SatValue CadicalSolver::solve()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  d_assumptions.clear();
  SatValue res = toSatValue(d_solver->solve());
  d_inSatMode = (res == SAT_VALUE_TRUE);
  ++d_statistics.d_numSatCalls;
  return res;
}

SatValue CadicalSolver::solve(long unsigned int&)
{
  Unimplemented() << "Setting limits for CaDiCaL not supported yet";
};

SatValue CadicalSolver::solve(const std::vector<SatLiteral>& assumptions)
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  d_assumptions.clear();
  for (const SatLiteral& lit : assumptions)
  {
    d_solver->assume(toCadicalLit(lit));
    d_assumptions.push_back(lit);
  }
  SatValue res = toSatValue(d_solver->solve());
  d_inSatMode = (res == SAT_VALUE_TRUE);
  ++d_statistics.d_numSatCalls;
  return res;
}

bool CadicalSolver::setPropagateOnly()
{
  d_solver->limit("decisions", 0); /* Gets reset after next solve() call. */
  return true;
}

void CadicalSolver::getUnsatAssumptions(std::vector<SatLiteral>& assumptions)
{
  for (const SatLiteral& lit : d_assumptions)
  {
    if (d_solver->failed(toCadicalLit(lit)))
    {
      assumptions.push_back(lit);
    }
  }
}

void CadicalSolver::interrupt() { d_solver->terminate(); }

SatValue CadicalSolver::value(SatLiteral l)
{
  Assert(d_inSatMode);
  return toSatValueLit(d_solver->val(toCadicalLit(l)));
}

SatValue CadicalSolver::modelValue(SatLiteral l)
{
  Assert(d_inSatMode);
  return value(l);
}

uint32_t CadicalSolver::getAssertionLevel() const
{
  Unreachable() << "CaDiCaL does not support assertion levels.";
}

bool CadicalSolver::ok() const { return d_inSatMode; }

CadicalSolver::Statistics::Statistics(StatisticsRegistry& registry,
                                      const std::string& prefix)
    : d_numSatCalls(registry.registerInt(prefix + "cadical::calls_to_solve")),
      d_numVariables(registry.registerInt(prefix + "cadical::variables")),
      d_numClauses(registry.registerInt(prefix + "cadical::clauses")),
      d_solveTime(registry.registerTimer(prefix + "cadical::solve_time"))
  {
}

/* CDCLTCadicalSolver ------------------------------------------------------- */

class CadicalPropagator : public CaDiCaL::ExternalPropagator
{
 public:
  CadicalPropagator(prop::TheoryProxy* proxy) : d_proxy(proxy) {}

  void notify_assignment(int lit, bool is_fixed) override
  {
    (void)is_fixed;
    if (d_decisions.size() == d_decisions_control.back())
    {
      SatLiteral slit(lit);
      d_decisions.push_back(slit);
      d_decision_vars.insert(slit.getSatVariable());
    }
  }

  void notify_new_decision_level() override
  {
    d_decisions_control.push_back(d_decisions.size());
  }

  void notify_backtrack(size_t level) override
  {
    Assert(d_proxy);
    d_proxy->notifyBacktrack(level);

    size_t cur_level = d_decisions_control.size();
    Assert(cur_level > level);
    for (; cur_level > level; --cur_level)
    {
      size_t idx = d_decisions_control.back();
      d_decisions_control.pop_back();
      for (size_t i = 0, n = d_decisions.size() - idx; i < n; ++i)
      {
        SatLiteral slit = d_decisions.back();
        d_decisions.pop_back();
        auto it = d_decision_vars.find(slit.getSatVariable());
        Assert(it != d_decision_vars.end());
        d_decision_vars.erase(*it);
      }
      Assert(d_decisions.size() == idx);
    }
  }

  bool cb_check_found_model(const std::vector<int>& model) override {}

  // int cb_decide () override;

  // int cb_propagate () override;

  // int cb_add_reason_clause_lit (int propagated_lit) override;

  const std::vector<SatLiteral>& get_decisions() const { return d_decisions; }

  bool is_decision(const SatVariable& var)
  {
    return d_decision_vars.find(var) != d_decision_vars.end();
  }

 private:
  /** The associated theory proxy. */
  prop::TheoryProxy* d_proxy = nullptr;
  std::vector<SatLiteral> d_decisions;
  std::vector<size_t> d_decisions_control;
  std::unordered_set<SatVariable> d_decision_vars;
};

CDCLTCadicalSolver::CDCLTCadicalSolver(Env& env,
                                       StatisticsRegistry& registry,
                                       const std::string& name)
    : CadicalSolver(registry, name), EnvObj(env), d_context(nullptr)
{
}

void CDCLTCadicalSolver::initialize(context::Context* context,
                                    prop::TheoryProxy* theoryProxy,
                                    context::UserContext* userContext,
                                    ProofNodeManager* pnm)
{
  d_context = context;
  d_proxy = theoryProxy;
  d_propagator.reset(new CadicalPropagator(theoryProxy));
}

void CDCLTCadicalSolver::push()
{
  d_context->push();  // SAT context for cvc5
}

void CDCLTCadicalSolver::pop()
{
  // TODO
  // Notify sat proof manager that we have popped and now potentially we need to
  // retrieve the proofs for the clauses inserted into optimized levels
  // if (needProof())
  //{
  //  d_pfManager->notifyPop();
  //}

  d_context->pop();  // SAT context for cvc5
}

void CDCLTCadicalSolver::resetTrail() {}

bool CDCLTCadicalSolver::properExplanation(SatLiteral lit,
                                           SatLiteral expl) const
{
}

void CDCLTCadicalSolver::requirePhase(SatLiteral lit) {}

bool CDCLTCadicalSolver::isDecision(SatVariable var) const
{
  return d_propagator->is_decision(var);
}

std::vector<SatLiteral> CDCLTCadicalSolver::getDecisions() const
{
  return d_propagator->get_decisions();
}

std::vector<Node> CDCLTCadicalSolver::getOrderHeap() const { return {}; }

int32_t CDCLTCadicalSolver::getDecisionLevel(SatVariable v) const {}

int32_t CDCLTCadicalSolver::getIntroLevel(SatVariable v) const {}

std::shared_ptr<ProofNode> CDCLTgetProof()
{
  // TODO
  return nullptr;
}

/* -------------------------------------------------------------------------- */
}  // namespace prop
}  // namespace cvc5::internal
