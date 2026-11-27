import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# AM–GM inequality, statement B (Gauss, blind formalization)

Source (issue TuriMath/am-gm-inequality#1, quoted exactly):
> For any non-negative real numbers x₁, …, xₙ, the geometric mean is at most the arithmetic
> mean: (x₁ x₂ ⋯ xₙ)^(1/n) ≤ (x₁ + x₂ + ⋯ + xₙ)/n, with equality if and only if
> x₁ = x₂ = ⋯ = xₙ.

Mapping, one line per part of the quote:
* "real numbers x₁, …, xₙ"            ↦ `n : ℕ` and a tuple `x : Fin n → ℝ` (xᵢ is `x i`)
* (n ≥ 1, per issue notes)            ↦ hypothesis `0 < n`
* "non-negative"                      ↦ hypothesis `∀ i, 0 ≤ x i`
* "x₁ x₂ ⋯ xₙ"                         ↦ `∏ i, x i`
* "(…)^(1/n)"                          ↦ real power `(∏ i, x i) ^ ((1 : ℝ) / n)` (`Real.rpow`)
* "(x₁ + x₂ + ⋯ + xₙ)/n"               ↦ `(∑ i, x i) / n`
* "geometric mean is at most …"       ↦ first conjunct, `≤`
* "with equality if and only if"      ↦ second conjunct, `GM = AM ↔ …`
* "x₁ = x₂ = ⋯ = xₙ"                   ↦ `∀ i j, x i = x j` (all entries pairwise equal)
-/

namespace TuriMath.AmGm.B

open Finset

/-- The geometric mean (x₁ ⋯ xₙ)^(1/n) of a tuple of `n` reals. -/
noncomputable def geomMean (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∏ i, x i) ^ ((1 : ℝ) / (n : ℝ))

/-- The arithmetic mean (x₁ + ⋯ + xₙ)/n of a tuple of `n` reals. -/
noncomputable def arithMean (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / (n : ℝ)

/-- AM–GM, unweighted, with its equality case. -/
def Statement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (x : Fin n → ℝ), (∀ i, 0 ≤ x i) →
    geomMean n x ≤ arithMean n x ∧
    (geomMean n x = arithMean n x ↔ ∀ i j, x i = x j)

/-! ## Sanity section: the hypotheses can all hold at once -/

/-- `n = 1`, `x = (0)`: `0 < n` and non-negativity hold together. -/
example : ∃ (n : ℕ) (x : Fin n → ℝ), 0 < n ∧ ∀ i, 0 ≤ x i :=
  ⟨1, fun _ => 0, Nat.one_pos, fun _ => le_rfl⟩

/-- A non-constant instance: `n = 2`, `x = (1, 4)`, hypotheses hold. -/
example : 0 < 2 ∧ ∀ i, 0 ≤ (![1, 4] : Fin 2 → ℝ) i := by
  refine ⟨by norm_num, ?_⟩
  intro i; fin_cases i <;> norm_num

/-! ## Concrete checks -/

/-- n = 2, x = (1, 4): GM = √4 = 2, AM = 5/2, so 2 ≤ 5/2 and they differ (entries differ). -/
example : geomMean 2 ![1, 4] = 2 := by
  unfold geomMean
  rw [Fin.prod_univ_two]
  norm_num

example : arithMean 2 ![1, 4] = 5 / 2 := by
  unfold arithMean
  rw [Fin.sum_univ_two]
  norm_num

/-- n = 3, x = (2, 2, 2): GM = (8)^(1/3) = 2 = AM, the equality case. -/
example : geomMean 3 ![2, 2, 2] = 2 := by
  unfold geomMean
  rw [Fin.prod_univ_three]
  norm_num

example : arithMean 3 ![2, 2, 2] = 2 := by
  unfold arithMean
  rw [Fin.sum_univ_three]
  norm_num

/-- n = 1, x = (7): GM = 7^1 = 7 = AM; a single number is trivially "all equal". -/
example : geomMean 1 ![7] = arithMean 1 ![7] := by
  unfold geomMean arithMean
  simp

end TuriMath.AmGm.B
