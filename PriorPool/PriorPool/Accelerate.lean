import RisingSea.Path
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Positivity

/-! A change of scale allowing a positive reserve weight at the origin. -/

namespace RisingSea.PriorPool

open Filter

private def accelerated (B : ℝ) (n : ℤ) : ℝ := (n : ℝ) * B ^ n.natAbs

private theorem accelerated_neg (B : ℝ) (n : ℤ) :
    accelerated B (-n) = -accelerated B n := by simp [accelerated]

private theorem accelerated_nonneg {B : ℝ} (hB : 1 < B) {n : ℤ} (hn : 0 ≤ n) :
    0 ≤ accelerated B n :=
  mul_nonneg (by exact_mod_cast hn) (pow_nonneg (by linarith) _)

/-- Each new positive point grows by more than the chosen factor. -/
private theorem accelerated_step {B : ℝ} (hB : 1 < B) {n : ℤ} (hn : 0 ≤ n) :
    B * accelerated B n < accelerated B (n + 1) := by
  have hexp : (n + 1).natAbs = n.natAbs + 1 := by
    lift n to ℕ using hn
    rfl
  rw [accelerated, accelerated, hexp, pow_succ, Int.cast_add, Int.cast_one]
  have hpos : 0 < B ^ n.natAbs * B := mul_pos (pow_pos (by linarith) _) (by linarith)
  linarith only [hpos]

private theorem bracket_nonnegative {B u v : ℝ} (hB : 1 < B)
    (hu : 0 < u) (hv : 0 < v) (hweight : u + v < 1) (hfast : 1 < v * B)
    {n : ℤ} (hn : 0 ≤ n) :
    accelerated B n < u * accelerated B n + v * accelerated B (n+1) ∧
      u * accelerated B n + v * accelerated B (n+1) < accelerated B (n+1) := by
  have hn₀ := accelerated_nonneg hB hn
  have hstep := accelerated_step hB hn
  have hinc : accelerated B n < accelerated B (n+1) :=
    (le_mul_of_one_le_left hn₀ hB.le).trans_lt hstep
  have hleft : accelerated B n < v * accelerated B (n+1) := calc
    _ ≤ (v * B) * accelerated B n := le_mul_of_one_le_left hn₀ hfast.le
    _ = v * (B * accelerated B n) := mul_assoc _ _ _
    _ < _ := mul_lt_mul_of_pos_left hstep hv
  refine ⟨by linarith [mul_nonneg hu.le hn₀], ?_⟩
  calc
    _ ≤ u * accelerated B (n+1) + v * accelerated B (n+1) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hinc.le hu.le) _
    _ = (u+v) * accelerated B (n+1) := (add_mul _ _ _).symm
    _ < _ := by simpa using mul_lt_mul_of_pos_right hweight (hn₀.trans_lt hinc)

private theorem bracket_all {B u v : ℝ} (hB : 1 < B)
    (hu : 0 < u) (hv : 0 < v) (hw : u + v < 1) (hfu : 1 < u * B) (hfv : 1 < v * B)
    (n : ℤ) :
    accelerated B n < u * accelerated B n + v * accelerated B (n+1) ∧
      u * accelerated B n + v * accelerated B (n+1) < accelerated B (n+1) := by
  by_cases hn : 0 ≤ n
  · exact bracket_nonnegative hB hu hv hw hfv hn
  · have hm : 0 ≤ -(n+1) := by omega
    have h := bracket_nonnegative hB hv hu (by linarith) hfu hm
    rw [show -(n + 1) + 1 = -n by omega, accelerated_neg, accelerated_neg] at h
    constructor <;> linarith [h.1, h.2]

/-- A common accelerated scale puts every three-input weighted pool in its edge gap,
with the third coefficient multiplying the value of the scale at vertex zero. -/
theorem exists_accelerated_vertices {a₀ a b : ℝ}
    (h₀ : 0 < a₀) (ha : 0 < a) (hb : 0 < b) (hs : a₀ + a + b = 1) :
    ∃ t : ℤ → ℝ, StrictMono t ∧ t 0 = 0 ∧ Tendsto t atTop atTop ∧ Tendsto t atBot atBot ∧
      ∀ n, t n < a * t (leftSignal n) + b * t (rightSignal n) ∧
        a * t (leftSignal n) + b * t (rightSignal n) < t (n+1) := by
  let B : ℝ := 2 + a⁻¹ + b⁻¹
  have ha' := inv_pos.mpr ha
  have hb' := inv_pos.mpr hb
  have hB : 1 < B := by dsimp [B]; linarith
  have hfa : 1 < a * B := by
    dsimp [B]
    nlinarith [mul_inv_cancel₀ ha.ne', mul_pos ha hb']
  have hfb : 1 < b * B := by
    dsimp [B]
    nlinarith [mul_inv_cancel₀ hb.ne', mul_pos hb ha']
  have hnormal := bracket_all hB ha hb (by linarith) hfa hfb
  have hreverse := bracket_all hB hb ha (by linarith) hfb hfa
  refine ⟨accelerated B, ?_, by simp [accelerated], ?_, ?_, ?_⟩
  · apply strictMono_int_of_lt_succ
    exact fun n => (hnormal n).1.trans (hnormal n).2
  · apply tendsto_atTop_mono' atTop _ (tendsto_intCast_atTop_atTop (R := ℝ))
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
    exact le_mul_of_one_le_right (by exact_mod_cast hn) (one_le_pow₀ hB.le)
  · have hcast : Tendsto (fun n : ℤ => (n : ℝ)) atBot atBot :=
      tendsto_intCast_atBot_iff.mpr tendsto_id
    refine tendsto_atBot_mono' atBot ?_ hcast
    filter_upwards [eventually_le_atBot (0 : ℤ)] with n hn
    change (n : ℝ) * B ^ n.natAbs ≤ n
    simpa using mul_le_mul_of_nonpos_left (one_le_pow₀ (n := n.natAbs) hB.le)
      (show (n : ℝ) ≤ 0 by exact_mod_cast hn)
  · intro n
    by_cases he : n % 2 = 0
    · simpa [leftSignal, rightSignal, he] using hnormal n
    · simpa [leftSignal, rightSignal, he, add_comm] using hreverse n

end RisingSea.PriorPool
