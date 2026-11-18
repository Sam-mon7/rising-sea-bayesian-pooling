import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace RisingSea.PriorPool

/-- Three observations identify the three coefficients of the pool, even
among unnormalized representations. Hold the first report fixed across
the first pair and the second report fixed across the second pair. -/
theorem pool_coefficients_identifiable {Ω : Type*} {P : ℝ} {X Y Z : Ω → ℝ}
    {wm w₀ wp : Ω} (hP : P ≠ 0)
    (hXm : X wm = X w₀) (hYm : Y wm ≠ Y w₀)
    (hYp : Y w₀ = Y wp) (hXp : X w₀ ≠ X wp) {u a b v c d : ℝ}
    (hp : ∀ w, Z w = u * P + a * X w + b * Y w)
    (hp' : ∀ w, Z w = v * P + c * X w + d * Y w) :
    u = v ∧ a = c ∧ b = d := by
  have offset (w : Ω) : (u - v) * P + (a - c) * X w + (b - d) * Y w = 0 := by
    linarith only [hp w, hp' w]
  have hb : b = d := by
    have hm := offset wm
    rw [hXm] at hm
    have eq : (b-d) * (Y wm - Y w₀) = 0 := by linarith only [hm, offset w₀]
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right (sub_ne_zero.mpr hYm))
  have ha : a = c := by
    have h := offset w₀
    rw [hYp] at h
    have eq : (a-c) * (X w₀ - X wp) = 0 := by linarith only [h, offset wp]
    exact sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right (sub_ne_zero.mpr hXp))
  have hu : u = v := by
    have h := offset w₀
    apply sub_eq_zero.mp
    simpa [ha, hb, hP, mul_eq_zero] using h
  exact ⟨hu, ha, hb⟩

end RisingSea.PriorPool
