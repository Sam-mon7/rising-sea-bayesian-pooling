import PriorPool
import Lean.Util.CollectAxioms

/-! Fail the check if a theorem or any of its dependencies uses a placeholder
or an axiom outside the usual foundational axioms of Lean and mathlib. -/
open Lean Elab Command in
elab "check_prior_axioms " decl:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let axioms ← collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "unexpected axiom {axiomName} in {name}"
  logInfo m!"{name} depends on {axioms.toList}"

check_prior_axioms RisingSea.PriorPool.all_three_positive
check_prior_axioms RisingSea.PriorPool.three_weight_link
check_prior_axioms RisingSea.PriorPool.truth_prior_half
check_prior_axioms RisingSea.PriorPool.exists_interlaced_knot_scale
check_prior_axioms RisingSea.PriorPool.exists_accelerated_vertices
check_prior_axioms RisingSea.PriorPool.pool_coefficients_identifiable
check_prior_axioms RisingSea.PriorPool.bounded_bayesian_pool_rigidity
check_prior_axioms RisingSea.PriorPool.right_endpoint_rigidity
check_prior_axioms RisingSea.PriorPool.left_endpoint_rigidity
