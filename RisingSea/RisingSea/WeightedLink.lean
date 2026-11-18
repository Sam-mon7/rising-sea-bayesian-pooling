import RisingSea.Path
import RisingSea.Link

namespace RisingSea

/-- For any fixed positive weights summing to one, one continuous increasing
change of scale realizes their weighted pool on every edge simultaneously. -/
theorem exists_weighted_path_link {p q : ℤ → ℝ} (hp : ∀ i, 0 < p i)
    (hq : StrictMono q) (a : ℝ) (ha : a ∈ Set.Ioo 0 1) :
    ∃ g : ℝ → ℝ, Continuous g ∧ StrictMono g ∧ ∀ n,
      g (q n) = a * g (leftReport p q n) + (1 - a) * g (rightReport p q n) := by
  let r (n : ℤ) := a * leftReport p q n + (1 - a) * rightReport p q n
  have hr (n : ℤ) : vertex p q n < r n ∧ r n < vertex p q (n + 1) := by
    have hgap := (vertex_strictMono hp hq) (show n < n + 1 by omega)
    have h₁ := mul_pos ha.1 (sub_pos.mpr hgap)
    have h₂ := mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hgap)
    by_cases he : n % 2 = 0 <;>
      simp [r, leftReport, rightReport, leftSignal, rightSignal, he] <;>
      constructor <;> nlinarith only [h₁, h₂]
  obtain ⟨g, hfix, hmap⟩ := exists_interlacing_orderIso (vertex p q) q r
    (vertex_strictMono hp hq) (vertex_interleaves hp hq) hr
  refine ⟨g, g.continuous, g.strictMono, fun n => ?_⟩
  simpa only [leftReport, rightReport, hfix, r] using hmap n

end RisingSea
