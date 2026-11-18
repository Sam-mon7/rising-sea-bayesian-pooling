import RisingSea
import PriorPool.Accelerate
import PriorPool.Bounded
import PriorPool.Identify
import PriorPool.KnotScale
import PriorPool.PriorMass
import PriorPool.Symmetric

/-!
# Positive weight on a prior and on two Bayesian reports

This module addresses the last conjecture of Dawid, DeGroot and Mortera,
section 4.5, page 283. All probabilities in the counterexample lie in (0,1).
-/

namespace RisingSea.PriorPool

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

abbrev Interior := Ioo (0 : ℝ) 1

private def half : Interior := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem vertex_mem (n : ℤ) : vertex mass rate n ∈ Interior :=
  ⟨(rate_range (n - 1)).1.trans (vertex_between mass_pos rate_strictMono n).1,
   (vertex_between mass_pos rate_strictMono n).2.trans (rate_range n).2⟩

private def V (n : ℤ) : Interior := ⟨vertex mass rate n, vertex_mem n⟩
private def Q (n : ℤ) : Interior := ⟨rate n, rate_range n⟩

/-- The same path law works for every weight triple. Translating the scale by
one gives the prior a nonzero transformed value. -/
theorem three_weight_link (a₀ a b : ℝ) (h₀ : 0 < a₀) (ha : 0 < a) (hb : 0 < b)
    (hs : a₀ + a + b = 1) :
    ∃ g : Interior ≃o ℝ, g half = 1 ∧ ∀ n : ℤ,
      g (Q n) = a₀ * g half + a * g (V (leftSignal n)) + b * g (V (rightSignal n)) := by
  obtain ⟨t, ht, ht0, htTop, htBot, hr⟩ :=
    exists_accelerated_vertices h₀ ha hb hs
  have hxc (y : ℝ) (hy : y ∈ Interior) :
      (∃ n, vertex mass rate n ≤ y) ∧ ∃ n, y < vertex mass rate n := by
    exact ⟨((vertex_bot.eventually (gt_mem_nhds hy.1)).mono (fun _ h => h.le)).exists,
      (vertex_top.eventually (lt_mem_nhds hy.2)).exists⟩
  have htc (y : ℝ) : (∃ n, t n ≤ y) ∧ ∃ n, y < t n :=
    ⟨(htBot.eventually (eventually_le_atBot y)).exists,
      (htTop.eventually (eventually_gt_atTop y)).exists⟩
  obtain ⟨f, hV, hQ⟩ := exists_interlaced_knot_scale (vertex mass rate) t rate
    (fun n => a * t (leftSignal n) + b * t (rightSignal n))
    (vertex_strictMono mass_pos rate_strictMono) ht vertex_mem rate_range hxc htc
    (vertex_interleaves mass_pos rate_strictMono) hr
  have hhalf : V 0 = half := Subtype.ext vertex_zero
  have hf0 : f half = 0 := by
    rw [← hhalf]
    exact (hV 0).trans ht0
  refine ⟨f.trans (OrderIso.addRight 1), ?_, ?_⟩
  · change f half + 1 = 1
    rw [hf0, zero_add]
  · intro n
    change f (Q n) + 1 = a₀ * (f half + 1) + a * (f (V _) + 1) + b * (f (V _) + 1)
    rw [show f (Q n) = _ from hQ n, show f (V (leftSignal n)) = _ from hV _,
      show f (V (rightSignal n)) = _ from hV _, hf0]
    linarith

/-- The probability data used in equation (24). All three reports are genuine
conditional expectations of the same event under the stated probability law. -/
structure Experiment where
  law : Measure World
  prior : Interior
  X : World → Interior
  Y : World → Interior
  Z : World → Interior
  probability : IsProbabilityMeasure law
  positive : ∀ s : Set World, s.Nonempty → 0 < law s
  prior_eq : (prior : ℝ) = (law truth).toReal
  left_calibrated : ∀ w, conditionalForecast law (fun v => (X v : ℝ)) w = X w
  right_calibrated : ∀ w, conditionalForecast law (fun v => (Y v : ℝ)) w = Y w
  joint_posterior : ∀ w,
    conditionalForecast law (fun v => ((X v : ℝ), (Y v : ℝ))) w = Z w
  informative : ∀ w, (X w < Z w ∧ Z w < Y w) ∨ (Y w < Z w ∧ Z w < X w)

/-- A fixed link and coefficient triple reproduce all pooled posteriors. -/
def Experiment.realizes (E : Experiment) (g : Interior ≃o ℝ) (u a b : ℝ) : Prop :=
  ∀ w, g (E.Z w) = u * g E.prior + a * g (E.X w) + b * g (E.Y w)

set_option maxHeartbeats 700000 in
/-- Both experts change the posterior everywhere. The law and all reports are
chosen before the three positive coefficients. One continuous increasing
bijection then implements the prescribed weights at every world. -/
theorem all_three_positive :
    ∃ E : Experiment, (E.prior : ℝ) = 1 / 2 ∧
      ∀ (a₀ a b : ℝ), 0 < a₀ → 0 < a → 0 < b → a₀ + a + b = 1 →
      ∃ g : Interior ≃o ℝ, Continuous g ∧ g E.prior = 1 ∧ E.realizes g a₀ a b ∧
        ∀ u' a' b' : ℝ, E.realizes g u' a' b' → a₀ = u' ∧ a = a' ∧ b = b' := by
  let μ := edgeLaw mass rate
  let X (w : World) := V (leftSignal w.1)
  let Y (w : World) := V (rightSignal w.1)
  let Z (w : World) := Q w.1
  obtain ⟨_, h⟩ := path_pool mass_pos mass_hasSum rate_strictMono rate_range
    (1 / 2) (by constructor <;> norm_num)
  letI : IsProbabilityMeasure μ := h.probability
  have hcell (w : World) :
      {v : World | ((X v : ℝ), (Y v : ℝ)) = ((X w : ℝ), (Y w : ℝ))} = edgeCell w.1 := by
    ext v
    exact (jointReport_injective mass_pos rate_strictMono).eq_iff
  let E : Experiment := {
    law := μ
    prior := half
    X := X
    Y := Y
    Z := Z
    probability := h.probability
    positive := h.regular
    prior_eq := (truth_prior_half mass_pos mass_hasSum rate_range mass_reflect rate_reflect).symm
    left_calibrated := fun w =>
      (conditionalForecast_eq_posterior μ (fun v => (X v : ℝ)) w
        (h.positive_cells w).1).trans (h.calibrated_left w)
    right_calibrated := fun w =>
      (conditionalForecast_eq_posterior μ (fun v => (Y v : ℝ)) w
        (h.positive_cells w).2.1).trans (h.calibrated_right w)
    joint_posterior := by
      intro w
      rw [conditionalForecast_eq_posterior μ (fun v => ((X v : ℝ), (Y v : ℝ)))
        w (h.regular _ ⟨w, rfl⟩), hcell]
      exact posterior_edgeCell mass_pos rate_range _
    informative := fun w => reports_bracket mass_pos rate_strictMono w.1 }
  refine ⟨E, rfl, ?_⟩
  intro a₀ a b h₀ ha hb hs
  obtain ⟨g, hprior, hpool⟩ := three_weight_link a₀ a b h₀ ha hb hs
  have hrep : E.realizes g a₀ a b := fun w => hpool w.1
  refine ⟨g, g.continuous, hprior, hrep, ?_⟩
  intro u' a' b' hrep'
  have vinj : Function.Injective V := by
    intro i j he
    exact (vertex_strictMono mass_pos rate_strictMono).injective (congrArg Subtype.val he)
  apply pool_coefficients_identifiable (P := g E.prior) (Z := fun w => g (E.Z w))
    (X := fun w => g (E.X w)) (Y := fun w => g (E.Y w))
    (wm := ((-1 : ℤ), true)) (w₀ := ((0 : ℤ), true)) (wp := ((1 : ℤ), true))
    (by rw [show g E.prior = 1 from hprior]; norm_num)
    (congrArg (g ∘ V) (by decide : leftSignal (-1) = leftSignal 0)) ?_
    (congrArg (g ∘ V) (by decide : rightSignal 0 = rightSignal 1)) ?_ hrep hrep'
  · exact (g.injective.comp vinj).ne (by decide : (-1 : ℤ) ≠ 1)
  · exact (g.injective.comp vinj).ne (by decide : (0 : ℤ) ≠ 2)

end
end RisingSea.PriorPool
