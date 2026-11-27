import Mathlib

/-!
# AM–GM inequality — statement A (Noether)

Source (issue TuriMath/am-gm-inequality#1, quoted exactly):
> For any non-negative real numbers x₁, …, xₙ, the geometric mean is at most the arithmetic
> mean: (x₁ x₂ ⋯ xₙ)^(1/n) ≤ (x₁ + x₂ + ⋯ + xₙ)/n, with equality if and only if
> x₁ = x₂ = ⋯ = xₙ.
-/

namespace TuriMath.AmGm.A

open Finset

/-- The unweighted AM–GM inequality with its equality case.

Mapping from the source quote to the Lean:
* "x₁, …, xₙ" — `n : ℕ` with `0 < n` (issue note: a positive number of variables), and
  `x : Fin n → ℝ`, an n-tuple indexed by `Fin n`.
* "real numbers" — codomain `ℝ`.
* "non-negative" — hypothesis `∀ i, 0 ≤ x i`.
* "(x₁ x₂ ⋯ xₙ)^(1/n)" — `(∏ i, x i) ^ ((1 : ℝ) / n)`, `Real.rpow` with a real exponent
  (the base is ≥ 0, so this is the usual real n-th root; `1/n` is real division, not ℕ division).
* "(x₁ + x₂ + ⋯ + xₙ)/n" — `(∑ i, x i) / n`, division in `ℝ` with `n` cast to `ℝ`.
* "the geometric mean is at most the arithmetic mean" — first conjunct, `≤`.
* "with equality if and only if x₁ = x₂ = ⋯ = xₙ" — second conjunct:
  `GM = AM ↔ ∀ i j, x i = x j` (all entries pairwise equal).
-/
def Statement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
    (∏ i, x i) ^ ((1 : ℝ) / n) ≤ (∑ i, x i) / n ∧
    ((∏ i, x i) ^ ((1 : ℝ) / n) = (∑ i, x i) / n ↔ ∀ i j, x i = x j)

/-! ## Sanity section
The hypotheses are `0 < n` and `∀ i, 0 ≤ x i`. They hold simultaneously, e.g. for `n = 1`
(and for `n = 3` with distinct entries, so the equality clause is not vacuous). -/

example : ∃ (n : ℕ) (x : Fin n → ℝ), 0 < n ∧ ∀ i, 0 ≤ x i :=
  ⟨1, fun _ => 0, Nat.one_pos, fun _ => le_rfl⟩

example : ∃ (n : ℕ) (x : Fin n → ℝ), 0 < n ∧ (∀ i, 0 ≤ x i) ∧ ¬ ∀ i j, x i = x j :=
  ⟨3, fun i => (i : ℝ), by norm_num, fun i => Nat.cast_nonneg _, fun h => by
    have := h 0 1
    norm_num at this⟩

end TuriMath.AmGm.A
