import RisingSea.Atoms
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Conditional expectation given the value of an observed report. -/

namespace RisingSea

open MeasureTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

/-- Conditional expectation of the binary outcome given the observed report. -/
def conditionalForecast {S : Type*} [mS : MeasurableSpace S] (μ : Measure World)
    (X : World → S) : World → ℝ := by
  classical
  exact condExp (mS.comap X) μ (truth.indicator (fun _ => (1 : ℝ)))

/-- On any positive-probability fibre, conditional expectation equals the ordinary Bayes ratio.
The report can take values in an uncountable space, for example a pair of real forecasts. -/
theorem conditionalForecast_eq_posterior {S : Type*} [mS : MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure World) [IsFiniteMeasure μ]
    (X : World → S) (w : World) (hpos : 0 < μ {v | X v = X w}) :
    conditionalForecast μ X w = posterior μ {v | X v = X w} := by
  classical
  let C : Set World := {v | X v = X w}
  let K := conditionalForecast μ X
  have hm : mS.comap X ≤ (inferInstance : MeasurableSpace World) :=
    (measurable_of_countable X).comap_le
  have hc : MeasurableSet[mS.comap X] C := ⟨{X w}, measurableSet_singleton _, rfl⟩
  have ht : MeasurableSet truth := (Set.to_countable _).measurableSet
  have hi : Integrable (truth.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator ht
  have hK : Measurable[mS.comap X] K := stronglyMeasurable_condExp.measurable
  have hconst (v : World) (hv : v ∈ C) : K v = K w := by
    obtain ⟨s, _, hs⟩ := hK (measurableSet_singleton (K w))
    have hw : w ∈ X ⁻¹' s := by rw [hs]; rfl
    have hv' : v ∈ X ⁻¹' s := by
      change X v ∈ s
      change X v = X w at hv
      rw [hv]
      exact hw
    rw [hs] at hv'
    exact hv'
  have havg : μ.real C * K w = μ.real (C ∩ truth) := calc
    _ = ∫ _ in C, K w ∂μ := by rw [setIntegral_const, smul_eq_mul]
    _ = ∫ v in C, K v ∂μ := setIntegral_congr_fun (hm _ hc) (fun v hv => (hconst v hv).symm)
    _ = ∫ v in C, truth.indicator (fun _ => (1 : ℝ)) v ∂μ := setIntegral_condExp hm hi hc
    _ = _ := by rw [setIntegral_indicator ht, setIntegral_const, smul_eq_mul, mul_one]
  apply (eq_div_iff (ENNReal.toReal_pos hpos.ne' (measure_ne_top μ C)).ne').2
  change K w * μ.real C = μ.real (truth ∩ C)
  simpa only [mul_comm (K w), Set.inter_comm truth] using havg

end
end RisingSea
