import RisingSea
import Lean.Util.CollectAxioms

/-! Check the transitive dependencies of the construction and its applications. -/

open Lean Elab Command in
elab "audit_axioms " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let axioms ← collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "unexpected axiom {axiomName} in {name}"
  logInfo m!"{name} depends on {axioms.toList}"

audit_axioms RisingSea.exists_interlacing_orderIso
audit_axioms RisingSea.conditionalForecast_eq_posterior
audit_axioms RisingSea.path_pool
audit_axioms RisingSea.all_weights_one_experiment
audit_axioms RisingSea.binary_pooling_counterexample
audit_axioms RisingSea.neither_expert_extraneous
audit_axioms RisingSea.conditional_expectation_counterexample
audit_axioms RisingSea.example_edge_zero

