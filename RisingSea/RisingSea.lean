import RisingSea.Conditioning
import RisingSea.WeightedLink
import RisingSea.Weights

/-!
# A coherent, equally weighted, transformed pool for a binary event

The marginal and joint posteriors below are evaluated on the fibres of the
*reported probabilities*. Every fibre used for conditioning has positive mass.
-/

namespace RisingSea

open MeasureTheory

def reportCell {α : Type*} (X : World → α) (w : World) : Set World :=
  {v | X v = X w}

def bothReports (X Y : World → ℝ) (w : World) : ℝ × ℝ := (X w, Y w)

/-- Two calibrated reports and their joint posterior for the binary event
`truth`, combined on a single scale using a fixed weight. -/
structure CoherentPool (μ : Measure World) (X Y : World → ℝ)
    (g : ℝ → ℝ) (a : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  regular : ∀ s : Set World, s.Nonempty → 0 < μ s
  link_continuous : Continuous g
  link_strictMono : StrictMono g
  report_range : ∀ w, X w ∈ Set.Ioo 0 1 ∧ Y w ∈ Set.Ioo 0 1
  calibrated_left : ∀ w, posterior μ (reportCell X w) = X w
  calibrated_right : ∀ w, posterior μ (reportCell Y w) = Y w
  strict_between : ∀ w, let z := posterior μ (reportCell (bothReports X Y) w)
                        (X w < z ∧ z < Y w) ∨ (Y w < z ∧ z < X w)
  fixed_pool : ∀ w, g (posterior μ (reportCell (bothReports X Y) w)) =
    a * g (X w) + (1 - a) * g (Y w)

theorem CoherentPool.positive_cells {μ : Measure World} {X Y : World → ℝ}
    {g : ℝ → ℝ} {a : ℝ} (h : CoherentPool μ X Y g a) (w : World) :
    0 < μ (reportCell X w) ∧ 0 < μ (reportCell Y w) ∧
      0 < μ (reportCell (bothReports X Y) w) :=
  ⟨h.regular _ ⟨w, rfl⟩, h.regular _ ⟨w, rfl⟩, h.regular _ ⟨w, rfl⟩⟩

/-- Every positive path law and every strictly increasing sequence of binary
event probabilities produce a calibrated pair and a single continuous link. -/
theorem path_pool {p q : ℤ → ℝ} (hp : ∀ n, 0 < p n) (hs : HasSum p 1)
    (hmono : StrictMono q) (hq : ∀ n, 0 < q n ∧ q n < 1)
    (a : ℝ) (ha : a ∈ Set.Ioo 0 1) :
    ∃ g : ℝ → ℝ, CoherentPool (edgeLaw p q)
      (fun w => leftReport p q w.1) (fun w => rightReport p q w.1) g a := by
  let X : World → ℝ := fun w => leftReport p q w.1
  let Y : World → ℝ := fun w => rightReport p q w.1
  have hX (w : World) : reportCell X w = pairCell (leftSignal w.1) := by
    ext v
    exact leftReport_eq_iff hp hmono v.1 w.1
  have hY (w : World) : reportCell Y w = pairCell (rightSignal w.1) := by
    ext v
    exact rightReport_eq_iff hp hmono v.1 w.1
  have hXY (w : World) : reportCell (bothReports X Y) w = edgeCell w.1 := by
    ext v
    exact (jointReport_injective hp hmono).eq_iff
  have hV (n : ℤ) : vertex p q n ∈ Set.Ioo 0 1 :=
    ⟨(hq (n-1)).1.trans (vertex_between hp hmono n).1,
     (vertex_between hp hmono n).2.trans (hq n).2⟩
  obtain ⟨g, hcont, hg, hpool⟩ := exists_weighted_path_link hp hmono a ha
  change ∃ g : ℝ → ℝ, CoherentPool (edgeLaw p q) X Y g a
  refine ⟨g, edgeLaw_probability hp hs hq, fun _ => edgeLaw_pos_of_nonempty hp hq,
    hcont, hg, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun w => ⟨hV (leftSignal w.1), hV (rightSignal w.1)⟩
  · intro w
    rw [hX]
    exact posterior_pairCell hp hq _
  · intro w
    rw [hY]
    exact posterior_pairCell hp hq _
  · intro w
    dsimp only
    rw [hXY, posterior_edgeCell hp hq]
    exact reports_bracket hp hmono _
  · intro w
    rw [hXY, posterior_edgeCell hp hq]
    exact hpool w.1

/-- One probability law and one pair of experts work for every weight chosen
in advance. The link can depend on that weight. -/
theorem all_weights_one_experiment :
    ∃ (μ : Measure World) (X Y : World → ℝ),
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∃ g : ℝ → ℝ, CoherentPool μ X Y g a := by
  obtain ⟨p, q, hp, hs, hmono, hq⟩ := exists_path_data
  exact ⟨_, _, _, path_pool hp hs hmono hq⟩

/-- Countably many worlds suffice for a counterexample to the normalized
generalized-linear pooling conjecture for two binary-event forecasts. -/
theorem binary_pooling_counterexample :
    ∃ (μ : Measure World) (X Y : World → ℝ) (g : ℝ → ℝ), CoherentPool μ X Y g (1/2) := by
  obtain ⟨μ, X, Y, hall⟩ := all_weights_one_experiment
  obtain ⟨g, h⟩ := hall (1/2) (by constructor <;> norm_num)
  exact ⟨_, _, _, g, h⟩

/-- Neither individual report gives the pooled posterior, on a set of mass one. -/
theorem neither_expert_extraneous {μ : Measure World} {X Y : World → ℝ} {g : ℝ → ℝ} {a : ℝ}
    (h : CoherentPool μ X Y g a) :
    μ {w | let z := posterior μ (reportCell (bothReports X Y) w)
           X w ≠ Y w ∧ z ≠ X w ∧ z ≠ Y w} = 1 := by
  letI := h.probability
  let D : Set World := {w | let z := posterior μ (reportCell (bothReports X Y) w)
                            X w ≠ Y w ∧ z ≠ X w ∧ z ≠ Y w}
  have hall : D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    rcases h.strict_between w with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact ⟨(hl.trans hr).ne, hl.ne', hr.ne⟩
    · exact ⟨(hr.trans hl).ne', hl.ne, hr.ne'⟩
  change μ D = 1
  rw [hall, measure_univ]

/-- The same counterexample in conditional-expectation notation.
`conditionalForecast μ R` is the conditional expectation of the binary
event indicator with respect to the sigma-algebra generated by report `R`. -/
theorem conditional_expectation_counterexample :
    ∃ (μ : Measure World) (X Y : World → ℝ) (g : ℝ → ℝ),
      IsProbabilityMeasure μ ∧ Continuous g ∧ StrictMono g ∧
      conditionalForecast μ X = X ∧ conditionalForecast μ Y = Y ∧
      ∀ w, let z := conditionalForecast μ (bothReports X Y) w
           ((X w < z ∧ z < Y w) ∨ (Y w < z ∧ z < X w)) ∧
           g z = (g (X w) + g (Y w)) / 2 := by
  obtain ⟨μ, X, Y, g, h⟩ := binary_pooling_counterexample
  letI := h.probability
  refine ⟨μ, X, Y, g, h.probability, h.link_continuous, h.link_strictMono, ?_, ?_, ?_⟩
  · funext w
    exact (conditionalForecast_eq_posterior μ X w (h.positive_cells w).1).trans
      (h.calibrated_left w)
  · funext w
    exact (conditionalForecast_eq_posterior μ Y w (h.positive_cells w).2.1).trans
      (h.calibrated_right w)
  · intro w
    dsimp only
    rw [conditionalForecast_eq_posterior μ (bothReports X Y) w (h.positive_cells w).2.2]
    refine ⟨h.strict_between w, ?_⟩
    calc
      _ = _ := h.fixed_pool w
      _ = _ := by ring

end RisingSea
