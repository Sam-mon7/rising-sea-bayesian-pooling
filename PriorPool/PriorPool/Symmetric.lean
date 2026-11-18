import RisingSea.Weights
import Mathlib.Topology.Order.DenselyOrdered

/-! A symmetric path law whose edge rates approach zero and one at the two ends. -/

noncomputable section

open Filter
open scoped Topology

namespace RisingSea.PriorPool

private def edgeReflection : ℤ ≃ ℤ where
  toFun n := -1 - n
  invFun n := -1 - n
  left_inv n := by change -1 - (-1 - n) = n; omega
  right_inv n := by change -1 - (-1 - n) = n; omega

/-- Symmetrize the normalized geometric path law across vertex zero. -/
def mass (n : ℤ) : ℝ := (exampleMass n + exampleMass (-1 - n)) / 2

/-- Use odd indices of the bounded, strictly increasing path rate. -/
def rate (n : ℤ) : ℝ := exampleRate (2*n + 1)

theorem mass_pos (n : ℤ) : 0 < mass n :=
  div_pos (add_pos (example_path_data.1 n) (example_path_data.1 _)) (by norm_num)

theorem mass_hasSum : HasSum mass 1 := by
  have h := example_path_data.2.1
  have hr := (edgeReflection.hasSum_iff (f := exampleMass)).2 h
  convert (h.add hr).div_const 2 using 1
  norm_num

theorem rate_strictMono : StrictMono rate := by
  intro i j hij
  exact example_path_data.2.2.1 (by omega : 2*i + 1 < 2*j + 1)

theorem rate_range (n : ℤ) : 0 < rate n ∧ rate n < 1 :=
  example_path_data.2.2.2 _

theorem mass_reflect (n : ℤ) : mass (-1-n) = mass n := by
  have h : -1 - (-1-n) = n := by omega
  simp only [mass, h, add_comm]

theorem rate_reflect (n : ℤ) : rate (-1-n) = 1 - rate n := by
  have h : 2*(-1-n)+1 = -(2*n+1) := by omega
  simp only [rate, h, exampleRate, Int.cast_neg, abs_neg]
  ring

theorem vertex_zero : vertex mass rate 0 = 1 / 2 := by
  have hm : mass (-1) = mass 0 := by simpa using mass_reflect 0
  have hr : rate (-1) = 1 - rate 0 := by simpa using rate_reflect 0
  simp only [vertex, zero_sub, hm, hr]
  apply (div_eq_iff (add_pos (mass_pos 0) (mass_pos 0)).ne').2
  ring

theorem rate_top : Tendsto rate atTop (𝓝 1) := by
  let e := orderIsoIooNegOneOne ℝ
  have hidx : Tendsto (fun n : ℤ => ((2*n+1 : ℤ) : ℝ)) atTop atTop := by
    apply tendsto_intCast_atTop_iff.mpr
    exact tendsto_atTop.2 fun b =>
      eventually_atTop.2 ⟨max b 0, fun n hn => by omega⟩
  have hc : Tendsto (fun n : ℤ => (e ((2*n+1 : ℤ) : ℝ)).val) atTop (𝓝 1) :=
    (tendsto_Ioo_atTop.mp (e.tendsto_atTop.comp hidx)).mono_right nhdsWithin_le_nhds
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hc).div_const 2
  rw [show ((1 + 1) / 2 : ℝ) = 1 by norm_num] at h
  have heq : rate = fun n : ℤ => (1 + (e ((2*n+1 : ℤ) : ℝ)).val) / 2 := by
    funext n
    unfold rate exampleRate e orderIsoIooNegOneOne
    rfl
  rwa [heq]

theorem rate_bot : Tendsto rate atBot (𝓝 0) := by
  have hrev : Tendsto (fun n : ℤ => -1-n) atBot atTop :=
    tendsto_atTop.2 fun b => eventually_atBot.2 ⟨-1-b, fun n hn => by omega⟩
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (rate_top.comp hrev)
  simpa [Function.comp_def, rate_reflect] using h

theorem vertex_top : Tendsto (vertex mass rate) atTop (𝓝 1) := by
  have hshift : Tendsto (fun n : ℤ => n-1) atTop atTop :=
    tendsto_atTop.2 fun b => eventually_atTop.2 ⟨b+1, fun n hn => by omega⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (rate_top.comp hshift) rate_top
    (fun n => (vertex_between mass_pos rate_strictMono n).1.le)
    (fun n => (vertex_between mass_pos rate_strictMono n).2.le)

theorem vertex_bot : Tendsto (vertex mass rate) atBot (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds rate_bot
    (fun n => ((rate_range (n-1)).1.trans (vertex_between mass_pos rate_strictMono n).1).le)
    (fun n => (vertex_between mass_pos rate_strictMono n).2.le)

end RisingSea.PriorPool
