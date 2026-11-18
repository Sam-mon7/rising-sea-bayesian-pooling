import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Two signals on a path

The edge indexed by `n : ℤ` joins vertices `n` and `n+1`. Its two signals
reveal the even and the odd endpoint, respectively. At a vertex the posterior
is the weighted average of the conditional event probabilities on its two
incident edges.
-/

noncomputable section

namespace RisingSea

/-- The even endpoint of the observed edge. -/
def leftSignal (n : ℤ) : ℤ := if n % 2 = 0 then n else n + 1

/-- The odd endpoint of the observed edge. -/
def rightSignal (n : ℤ) : ℤ := if n % 2 = 0 then n + 1 else n

theorem leftSignal_eq_iff (i n : ℤ) :
    leftSignal i = leftSignal n ↔ i = leftSignal n - 1 ∨ i = leftSignal n := by
  by_cases hi : i % 2 = 0 <;> by_cases hn : n % 2 = 0 <;> simp [leftSignal, hi, hn] <;> omega

theorem rightSignal_eq_iff (i n : ℤ) :
    rightSignal i = rightSignal n ↔ i = rightSignal n - 1 ∨ i = rightSignal n := by
  by_cases hi : i % 2 = 0 <;> by_cases hn : n % 2 = 0 <;> simp [rightSignal, hi, hn] <;> omega

theorem jointSignal_injective :
    Function.Injective (fun n : ℤ => (leftSignal n, rightSignal n)) := by
  intro i n h
  have hl : leftSignal i = leftSignal n := congrArg Prod.fst h
  have hr : rightSignal i = rightSignal n := congrArg Prod.snd h
  by_cases hi : i % 2 = 0 <;> by_cases hn : n % 2 = 0 <;>
    simp [leftSignal, rightSignal, hi, hn] at hl hr <;> omega

/-- The posterior on seeing either endpoint when the edge weights are `p`
and the event probability on each edge is `q`. -/
def vertex (p q : ℤ → ℝ) (n : ℤ) : ℝ :=
  (p (n - 1) * q (n - 1) + p n * q n) / (p (n - 1) + p n)

private theorem weighted_mean_between {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (huv : u < v) :
    u < (a * u + b * v) / (a + b) ∧ (a * u + b * v) / (a + b) < v := by
  constructor
  · apply (lt_div_iff₀ (add_pos ha hb)).2
    nlinarith [mul_pos hb (sub_pos.mpr huv)]
  · apply (div_lt_iff₀ (add_pos ha hb)).2
    nlinarith [mul_pos ha (sub_pos.mpr huv)]

variable {p q : ℤ → ℝ}

theorem vertex_between (hp : ∀ i, 0 < p i) (hq : StrictMono q) (n : ℤ) :
    q (n - 1) < vertex p q n ∧ vertex p q n < q n :=
  weighted_mean_between (hp _) (hp _) (hq (by omega : n-1 < n))

theorem vertex_interleaves (hp : ∀ i, 0 < p i) (hq : StrictMono q) (n : ℤ) :
    vertex p q n < q n ∧ q n < vertex p q (n + 1) := by
  refine ⟨(vertex_between hp hq n).2, ?_⟩
  simpa using (vertex_between hp hq (n + 1)).1

theorem vertex_strictMono (hp : ∀ i, 0 < p i) (hq : StrictMono q) :
    StrictMono (vertex p q) := by
  apply strictMono_int_of_lt_succ
  intro n
  exact (vertex_interleaves hp hq n).1.trans (vertex_interleaves hp hq n).2

def leftReport (p q : ℤ → ℝ) (n : ℤ) : ℝ := vertex p q (leftSignal n)

def rightReport (p q : ℤ → ℝ) (n : ℤ) : ℝ := vertex p q (rightSignal n)

/-- On every edge, the two individual reports strictly bracket the joint
report. Their order depends only on which endpoint has the even index. -/
theorem reports_bracket (hp : ∀ i, 0 < p i) (hq : StrictMono q) (n : ℤ) :
    (leftReport p q n < q n ∧ q n < rightReport p q n) ∨
    (rightReport p q n < q n ∧ q n < leftReport p q n) := by
  by_cases he : n % 2 = 0
  · exact Or.inl (by simpa [leftReport, rightReport, leftSignal, rightSignal, he] using
      vertex_interleaves hp hq n)
  · exact Or.inr (by simpa [leftReport, rightReport, leftSignal, rightSignal, he] using
      vertex_interleaves hp hq n)

theorem leftReport_eq_iff (hp : ∀ i, 0 < p i) (hq : StrictMono q) (i n : ℤ) :
    leftReport p q i = leftReport p q n ↔ i = leftSignal n - 1 ∨ i = leftSignal n := by
  exact (vertex_strictMono hp hq).injective.eq_iff.trans (leftSignal_eq_iff i n)

theorem rightReport_eq_iff (hp : ∀ i, 0 < p i) (hq : StrictMono q) (i n : ℤ) :
    rightReport p q i = rightReport p q n ↔ i = rightSignal n - 1 ∨ i = rightSignal n := by
  exact (vertex_strictMono hp hq).injective.eq_iff.trans (rightSignal_eq_iff i n)

theorem jointReport_injective (hp : ∀ i, 0 < p i) (hq : StrictMono q) :
    Function.Injective (fun n : ℤ => (leftReport p q n, rightReport p q n)) := by
  intro i n h
  apply jointSignal_injective
  exact Prod.ext ((vertex_strictMono hp hq).injective (congrArg Prod.fst h))
    ((vertex_strictMono hp hq).injective (congrArg Prod.snd h))

end RisingSea
