import Theorems.AmGm.A
import Theorems.AmGm.B
import Theorems.AmGm.Equiv

/-!
# AM–GM: proof (Euler)

Self-contained proof from `t ≤ exp (t - 1)` (`Real.add_one_le_exp`, strict off `t = 1`),
not via Mathlib's AM–GM. With `a = AM > 0`: `∏ x i / a ≤ exp (∑ (x i / a - 1)) = exp 0 = 1`,
so `∏ x ≤ aⁿ`, with equality only if every `x i = a`.
-/

namespace TuriMath.AmGm

open Finset

private lemma key (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ha : 0 < (∑ i, x i) / n) :
    ∏ i, x i ≤ ((∑ i, x i) / n) ^ n ∧
      (∏ i, x i = ((∑ i, x i) / n) ^ n → ∀ i, x i = (∑ i, x i) / n) := by
  set a := (∑ i, x i) / (n : ℝ) with ha_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i, (x i / a - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : ∑ i, x i = n * a := by rw [ha_def]; field_simp
    rw [this]; field_simp; ring
  have hpe : ∏ i, Real.exp (x i / a - 1) = 1 := by
    rw [← Real.exp_sum, hsum, Real.exp_zero]
  have hprod : ∏ i, x i / a = (∏ i, x i) / a ^ n := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hle : ∀ i ∈ (univ : Finset (Fin n)), x i / a ≤ Real.exp (x i / a - 1) := fun i _ => by
    linarith [Real.add_one_le_exp (x i / a - 1)]
  have hapos : 0 < a ^ n := pow_pos ha n
  have h1 : (∏ i, x i) / a ^ n ≤ 1 := by
    rw [← hprod, ← hpe]
    exact Finset.prod_le_prod₀ (fun i _ => div_nonneg (hx i) ha.le) hle
  refine ⟨by rwa [div_le_one hapos] at h1, fun heq => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hne
  by_cases hP : ∏ i, x i = 0
  · rw [hP] at heq; exact absurd heq.symm hapos.ne'
  have hxpos : ∀ i, 0 < x i := fun i =>
    lt_of_le_of_ne (hx i) (fun h => hP (Finset.prod_eq_zero (mem_univ i) h.symm))
  have hlt : ∑ i, Real.log (x i / a) < ∑ i, (x i / a - 1) := by
    refine Finset.sum_lt_sum (fun i _ => Real.log_le_sub_one_of_pos (div_pos (hxpos i) ha))
      ⟨j, mem_univ j, Real.log_lt_sub_one_of_pos (div_pos (hxpos j) ha) ?_⟩
    intro h; apply hj; field_simp at h; linarith
  have hpr : ∏ i, x i / a = Real.exp (∑ i, Real.log (x i / a)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Real.exp_log (div_pos (hxpos i) ha)).symm
  have h2 : ∏ i, x i / a < 1 := by
    rw [hpr, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (hsum ▸ hlt)
  rw [hprod, heq, div_self hapos.ne'] at h2
  exact lt_irrefl _ h2

theorem main : A.Statement := by
  intro n hn x hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hP : 0 ≤ ∏ i, x i := Finset.prod_nonneg fun i _ => hx i
  have hS : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  set a := (∑ i, x i) / (n : ℝ) with ha_def
  have ha0 : 0 ≤ a := div_nonneg hS hn'.le
  have hn1 : (n : ℝ) * (1 / n) = 1 := by field_simp
  -- constant tuples
  have hconst : (∀ i j, x i = x j) → (∏ i, x i) ^ ((1 : ℝ) / n) = a := by
    intro h
    obtain ⟨k⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hc : ∀ i, x i = x k := fun i => h i k
    have e1 : ∏ i, x i = x k ^ n := by simp [hc]
    have e2 : a = x k := by
      rw [ha_def]; simp [hc]; field_simp
    rw [e1, e2, ← Real.rpow_natCast, ← Real.rpow_mul (hx k), mul_one_div_cancel hn'.ne',
      Real.rpow_one]
  by_cases hazero : a = 0
  · -- all entries zero
    have hz : ∀ i, x i = 0 := by
      have h0 : ∑ i, x i = 0 := by
        rw [ha_def] at hazero
        rcases div_eq_zero_iff.mp hazero with h | h
        · exact h
        · exact absurd h hn'.ne'
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hx i).mp h0 i (mem_univ i)
    have hgm : (∏ i, x i) ^ ((1 : ℝ) / n) = a := hconst fun i j => by rw [hz i, hz j]
    refine ⟨hgm.le, ⟨fun _ i j => by rw [hz i, hz j], fun _ => hgm⟩⟩
  have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hazero)
  obtain ⟨hk1, hk2⟩ := key n hn x hx ha
  have hle : (∏ i, x i) ^ ((1 : ℝ) / n) ≤ a := by
    calc (∏ i, x i) ^ ((1 : ℝ) / n) ≤ (a ^ n) ^ ((1 : ℝ) / n) :=
          Real.rpow_le_rpow hP hk1 (by positivity)
      _ = a := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha0, mul_one_div_cancel hn'.ne',
            Real.rpow_one]
  refine ⟨hle, ⟨fun heq => ?_, fun h => hconst h⟩⟩
  have hPeq : ∏ i, x i = a ^ n := by
    have : ((∏ i, x i) ^ ((1 : ℝ) / n)) ^ n = a ^ n := by rw [heq]
    rw [← this, ← Real.rpow_natCast, ← Real.rpow_mul hP, one_div_mul_cancel hn'.ne',
      Real.rpow_one]
  have hall := hk2 hPeq
  intro i j; rw [hall i, hall j]

end TuriMath.AmGm
