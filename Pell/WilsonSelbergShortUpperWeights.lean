/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE file.
Author: Arend Mellendijk
Pinned-Mathlib adaptation for the Pell project.
-/

import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.NumberTheory.SelbergSieve

/-!
# Short Selberg upper weights for Wilson's neutralizer

This is a pinned-Mathlib port of the finite optimal-weight package in
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean` at commit
`a5154676af9aa3095150ee410cdda80555aa0642`.

Mathlib already proves that `lambdaSquared` weights are upper-Moebius and
diagonalizes their main term.  The declarations below supply the missing
cutoff-optimal base weight, its support and size bounds, and the exact
reciprocal truncated-mass main term.  No prime-distribution estimate is
asserted in this file.
-/

namespace PellPaper

open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega BigOperators

open Finset Real Nat ArithmeticFunction

noncomputable section

private theorem main4MoebiusInvDvdLowerBoundInt
    (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then μ d else 0) =
      if l = m then μ l else 0 := by
  have hmPos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ ↦ Squarefree.squarefree_of_dvd)).mpr
  intro m hmPos hm
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y ↦ μ x • if l = y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul,
        ← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime,
        hmul]
      apply coprime_of_squarefree_mul
      rw [hmul]
      exact hm
    · intro d _hd hdl
      rw [if_neg hdl.symm, smul_zero]
    · intro hnot
      rw [mem_divisors] at hnot
      exact (hnot ⟨hl, (Nat.ne_of_gt hmPos)⟩).elim
  · rw [if_neg hl, sum_eq_zero]
    intro d hd
    rw [if_neg, smul_zero]
    intro hdl
    subst d
    exact hl (dvd_of_mem_divisors hd)

private theorem main4MoebiusInvDvdLowerBoundIntOn
    {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) =
      if l = m then μ l else 0 := by
  calc
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) =
        ∑ d ∈ P.divisors, if d ∣ m then (if l ∣ d then μ d else 0) else 0 := by
      apply sum_congr rfl
      intro d _hd
      by_cases hld : l ∣ d <;> by_cases hdm : d ∣ m <;> simp_all
    _ = ∑ d ∈ P.divisors.filter (fun d ↦ d ∣ m),
        if l ∣ d then μ d else 0 := by
      rw [sum_filter]
    _ = ∑ d ∈ m.divisors, if l ∣ d then μ d else 0 := by
      rw [Nat.divisors_filter_dvd_of_dvd hP.ne_zero hm]
    _ = if l = m then μ l else 0 :=
      main4MoebiusInvDvdLowerBoundInt l m (hP.squarefree_of_dvd hm)

private theorem main4MoebiusInvDvdLowerBoundReal
    {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  exact main4MoebiusInvDvdLowerBoundIntOn hP l m hm

private theorem main4LambdaSquaredEqZeroOfSupportWlog
    {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0)
    {d d₁ d₂ : ℕ} (hd : ¬(d : ℝ) ≤ y)
    (h : d = Nat.lcm d₁ d₂) (hle : d₁ ≤ d₂) :
    w d₁ * w d₂ = 0 := by
  rw [hw d₂, mul_zero]
  intro hd₂
  apply hd
  apply le_trans _ hd₂
  norm_cast
  calc
    d ≤ d₁ * d₂ := by
      rw [h]
      by_cases h₁ : d₁ = 0
      · simp [h₁]
      by_cases h₂ : d₂ = 0
      · simp [h₂]
      exact Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero h₁)
        (Nat.pos_of_ne_zero h₂)) (Nat.lcm_dvd_mul d₁ d₂)
    _ ≤ d₂ ^ 2 := by
      rw [sq]
      gcongr

/-- If the base weights vanish above square-root level, their `Lambda^2`
upper coefficients vanish above the level itself. -/
theorem main4LambdaSquared_eq_zero_of_support
    (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0)
    (d : ℕ) (hd : ¬(d : ℝ) ≤ y) :
    BoundingSieve.lambdaSquared w d = 0 := by
  unfold BoundingSieve.lambdaSquared
  by_cases hy : 0 ≤ y
  · apply sum_eq_zero
    intro d₁ _hd₁
    apply sum_eq_zero
    intro d₂ _hd₂
    split_ifs with h
    · rcases Nat.le_or_le d₁ d₂ with hle | hle
      · exact main4LambdaSquaredEqZeroOfSupportWlog hw hd h hle
      · rw [mul_comm]
        exact main4LambdaSquaredEqZeroOfSupportWlog hw hd
          (Nat.lcm_comm d₁ d₂ ▸ h) hle
    · rfl
  · have hall : ∀ e : ℕ, w e = 0 := by
      intro e
      apply hw e
      have he : (0 : ℝ) ≤ e ^ 2 := by positivity
      linarith
    apply sum_eq_zero
    intro d₁ _hd₁
    apply sum_eq_zero
    intro d₂ _hd₂
    rw [hall d₁, hall d₂]
    simp

/-- Reindex a divisor sum by multiplication.  This is the finite change of
variables used in the cutoff Selberg optimizer. -/
theorem main4SumMulSubst
    (k n : ℕ) {f : ℕ → ℝ}
    (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
    (∑ l ∈ n.divisors, f l) =
      ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  · calc
      (∑ l ∈ n.divisors, f l) =
          ∑ l ∈ n.divisors, ∑ m ∈ n.divisors,
            if l = k * m then f l else 0 := by
        apply sum_congr rfl
        intro l hl
        by_cases hkl : k ∣ l
        · rw [sum_eq_single (l / k)]
          · rw [if_pos (Nat.mul_div_cancel' hkl).symm]
          · intro m _hm hne
            rw [if_neg]
            intro hlkm
            apply hne
            rw [hlkm, Nat.mul_div_cancel_left]
            exact Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
          · intro hnot
            rw [mem_divisors] at hnot
            exact (hnot ⟨(Nat.div_dvd_of_dvd hkl).trans
              (dvd_of_mem_divisors hl), hn⟩).elim
        · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero]
          intro m _hm
          simp
      _ = ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro m _hm
        by_cases hdvd : k * m ∣ n
        · rw [if_pos hdvd, sum_ite_eq_of_mem']
          rw [mem_divisors]
          exact ⟨hdvd, hn⟩
        · rw [if_neg hdvd, sum_eq_zero]
          intro l hl
          rw [if_neg]
          rintro rfl
          exact hdvd (dvd_of_mem_divisors hl)
  · rw [sum_eq_zero, sum_eq_zero]
    · intro m _hm
      rw [if_neg]
      intro hkm
      exact hkn ((Nat.dvd_mul_right k m).trans hkm)
    · intro l hl
      exact h l (dvd_of_mem_divisors hl)
        (fun hkl ↦ hkn (hkl.trans (dvd_of_mem_divisors hl)))

/-- The truncated Selberg mass `G = ∑_{l | P, l² ≤ y} g(l)`. -/
def main4SelbergBoundingSum (s : SelbergSieve) : ℝ :=
  let B := s.toBoundingSieve
  ∑ l ∈ B.prodPrimes.divisors,
    if (l : ℝ) ^ 2 ≤ s.level then B.selbergTerms l else 0

/-- The cutoff-optimal Selberg base weights. -/
def main4SelbergWeights (s : SelbergSieve) : ℕ → ℝ := fun d ↦
  let B := s.toBoundingSieve
  if d ∣ B.prodPrimes then
    (B.nu d)⁻¹ * B.selbergTerms d * (μ d : ℝ) *
      (main4SelbergBoundingSum s)⁻¹ *
      ∑ m ∈ B.prodPrimes.divisors,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
          B.selbergTerms m
        else 0
  else 0

/-- The resulting short upper-Moebius coefficients. -/
def main4SelbergMuPlus (s : SelbergSieve) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (main4SelbergWeights s)

theorem main4SelbergBoundingSum_pos (s : SelbergSieve) :
    0 < main4SelbergBoundingSum s := by
  let B := s.toBoundingSieve
  unfold main4SelbergBoundingSum
  dsimp only
  rw [← sum_filter]
  apply sum_pos
  · intro l hl
    simp only [mem_filter, mem_divisors] at hl
    exact B.selbergTerms_pos hl.1.1
  · refine ⟨1, ?_⟩
    simp only [mem_filter]
    refine ⟨one_mem_divisors.mpr B.prodPrimes_ne_zero, ?_⟩
    simpa using s.one_le_level

theorem main4SelbergBoundingSum_ne_zero (s : SelbergSieve) :
    main4SelbergBoundingSum s ≠ 0 :=
  ne_of_gt (main4SelbergBoundingSum_pos s)

theorem main4SelbergWeights_eq_zero_of_not_dvd
    (s : SelbergSieve) {d : ℕ}
    (hd : ¬ d ∣ s.toBoundingSieve.prodPrimes) :
    main4SelbergWeights s d = 0 := by
  rw [main4SelbergWeights, if_neg hd]

theorem main4SelbergWeights_eq_zero
    (s : SelbergSieve) (d : ℕ)
    (hd : ¬(d : ℝ) ^ 2 ≤ s.level) :
    main4SelbergWeights s d = 0 := by
  unfold main4SelbergWeights
  dsimp only
  split_ifs with hdP
  · rw [mul_eq_zero_of_right]
    apply sum_eq_zero
    intro m hm
    rw [if_neg]
    intro hdm
    apply hd
    exact le_trans (by
      norm_cast
      exact Nat.pow_le_pow_left
        (Nat.le_mul_of_pos_right d (Nat.pos_of_mem_divisors hm)) 2) hdm.1
  · rfl

section SelbergOptimizer

variable (s : SelbergSieve)

set_option quotPrecheck false
local notation3 "ν" =>
  BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" =>
  BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" =>
  BoundingSieve.selbergTerms (s := SelbergSieve.toBoundingSieve (self := s))
local notation "y" => s.level
local notation "S" => main4SelbergBoundingSum s
local notation "γ" => main4SelbergWeights s
local notation "μ⁺" => main4SelbergMuPlus s

theorem main4SelbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * (μ d : ℝ) := by
  unfold main4SelbergWeights
  dsimp only
  rw [if_pos hdP, mul_assoc]
  trans ((μ d : ℝ) ^ 2 * (ν d)⁻¹ * g d * S⁻¹ *
      ∑ m ∈ divisors P,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0)
  swap
  · apply le_of_eq
    ring
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (inv_nonneg.mpr (le_of_lt
            (s.toBoundingSieve.nu_pos_of_dvd_prodPrimes hdP))))
        (le_of_lt (s.toBoundingSieve.selbergTerms_pos hdP)))
      (inv_nonneg.mpr (le_of_lt (main4SelbergBoundingSum_pos s)))
  · apply sum_nonneg
    intro m hm
    split_ifs
    · exact le_of_lt
        (s.toBoundingSieve.selbergTerms_pos (dvd_of_mem_divisors hm))
    · rfl

/-- The cutoff-optimal base weight has the expected upper-divisor transform. -/
theorem main4SelbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * (μ d : ℝ) *
        ∑ l ∈ divisors P,
          if d ∣ l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0 := by
  by_cases hdP : d ∣ P
  swap
  · unfold main4SelbergWeights
    dsimp only
    rw [if_neg hdP]
    rw [sum_eq_zero]
    · ring
    intro l hl
    rw [mem_divisors] at hl
    rw [if_neg]
    intro hdl
    exact hdP (hdl.1.trans hl.1)
  unfold main4SelbergWeights
  dsimp only
  rw [if_pos hdP]
  repeat' rw [mul_sum]
  apply Eq.symm
  rw [main4SumMulSubst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ← ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ (fun _ ↦ rfl)
    · rw [coprime_comm]
      constructor
      · intro h
        exact ⟨by exact_mod_cast h.2.2, coprime_of_squarefree_mul
          (s.toBoundingSieve.prodPrimes_squarefree.squarefree_of_dvd h.1)⟩
      · intro h
        exact ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd h.2 hdP
            (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, by exact_mod_cast h.1⟩
    · intro h
      trans (ν d)⁻¹ * ν d * g d * (μ d : ℝ) / S * g m
      · rw [inv_mul_cancel₀ (s.toBoundingSieve.nu_ne_zero hdP),
          s.toBoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime
            (coprime_comm.mp h.2)]
        ring
      · ring
  · intro l _hl hdl
    rw [if_neg, mul_zero]
    intro h
    exact hdl h.1

/-- Exact diagonal coordinates of the cutoff-optimal base weight. -/
theorem main4SelbergWeights_diagonalization
    (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if (l : ℝ) ^ 2 ≤ y then g l * (μ l : ℝ) * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ y then
            g k * S⁻¹ * (μ d : ℝ)
          else 0 := by
      apply sum_congr rfl
      intro d _hd
      rw [main4SelbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl
      intro k _hk
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ ↦ rfl)
      intro _h
      ring
    _ = ∑ k ∈ divisors P,
        if (k : ℝ) ^ 2 ≤ y then
          (∑ d ∈ divisors P,
            if l ∣ d ∧ d ∣ k then (μ d : ℝ) else 0) * g k * S⁻¹
        else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _hk
      apply Eq.symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum]
      apply sum_congr rfl
      intro d _hd
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ← ite_and]
      apply if_ctx_congr _ _ (fun _ ↦ rfl)
      · tauto
      · intro _h
        ring
    _ = if (l : ℝ) ^ 2 ≤ y then
        g l * (μ l : ℝ) * S⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors P) l
        (fun _ ↦ if (l : ℝ) ^ 2 ≤ y then
          g l * (μ l : ℝ) * S⁻¹ else 0) hl]
      apply sum_congr rfl
      intro k hk
      rw [main4MoebiusInvDvdLowerBoundReal
          s.toBoundingSieve.prodPrimes_squarefree l k (dvd_of_mem_divisors hk),
        ← ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ (fun _ ↦ rfl)
      · rw [and_comm, eq_comm]
        apply and_congr_right
        intro heq
        rw [heq]
      · intro h
        rw [h.1]
        ring

/-- The cutoff-optimal base weight is normalized at one. -/
theorem main4SelbergWeight_one : γ 1 = 1 := by
  unfold main4SelbergWeights
  dsimp only
  rw [if_pos (one_dvd P), s.toBoundingSieve.nu_mult.map_one,
    s.toBoundingSieve.selbergTerms_isMultiplicative.map_one]
  simp only [inv_one, mul_one, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, one_mul]
  simp
  unfold main4SelbergBoundingSum
  dsimp only
  rw [inv_mul_cancel₀]
  exact main4SelbergBoundingSum_ne_zero s

/-- The Selberg coefficients are an honest upper-Moebius neutralizer. -/
theorem main4SelbergMuPlus_isUpperMoebius :
    BoundingSieve.IsUpperMoebius μ⁺ := by
  exact BoundingSieve.upperMoebius_lambdaSquared γ
    (main4SelbergWeight_one s)

/-- The Selberg upper coefficients are supported at the declared level. -/
theorem main4SelbergMuPlus_eq_zero
    (d : ℕ) (hd : ¬(d : ℝ) ≤ y) : μ⁺ d = 0 := by
  apply main4LambdaSquared_eq_zero_of_support γ y _ d hd
  exact main4SelbergWeights_eq_zero s

/-- The main sum of the cutoff-optimal `Lambda^2` coefficients is exactly
the reciprocal truncated Selberg mass. -/
theorem main4Selberg_mainSum_eq_inv :
    s.toBoundingSieve.mainSum μ⁺ = S⁻¹ := by
  unfold main4SelbergMuPlus
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  trans ∑ l ∈ divisors P,
      if (l : ℝ) ^ 2 ≤ y then g l * (S⁻¹) ^ 2 else 0
  · apply sum_congr rfl
    intro l hl
    rw [main4SelbergWeights_diagonalization s l hl,
      ite_pow, zero_pow (by norm_num : 2 ≠ 0), mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (g l)⁻¹ * g l * g l * (μ l : ℝ) ^ 2 * (S⁻¹) ^ 2
    · ring
    have hmu : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hl)
    rw [hmu]
    rw [inv_mul_cancel₀
      (ne_of_gt (s.toBoundingSieve.selbergTerms_pos
        (dvd_of_mem_divisors hl)))]
    ring
  · simp_rw [← ite_zero_mul]
    rw [← sum_mul]
    change S * (S⁻¹) ^ 2 = S⁻¹
    rw [sq, ← mul_assoc,
      mul_inv_cancel₀ (main4SelbergBoundingSum_ne_zero s), one_mul]

private theorem main4EqGcdMulOfDvdOfCoprime
    {k d m : ℕ} (hkd : k ∣ d) (hmd : m.Coprime d) (hk : k ≠ 0) :
    k = d.gcd (k * m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by
    use k
    rw [mul_comm]
    exact hr
  apply Eq.symm
  rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  exact hmd.coprime_dvd_right hrdvd

private theorem main4SelbergGcdProductIff
    {k m d : ℕ} (hkd : k ∣ d)
    (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧
        ((k * m : ℕ) : ℝ) ^ 2 ≤ y ↔
      ((k * m : ℕ) : ℝ) ^ 2 ≤ y ∧ m.Coprime d := by
  constructor
  · intro h
    refine ⟨h.2.2, ?_⟩
    obtain ⟨r, hr⟩ := hkd
    rw [hr, Nat.gcd_mul_left, eq_comm,
      mul_eq_left₀ (by rintro rfl; simp at hk)] at h
    rw [hr, coprime_comm]
    apply Coprime.mul_left
    · exact coprime_of_squarefree_mul
        (s.toBoundingSieve.prodPrimes_squarefree.squarefree_of_dvd h.1)
    · exact h.2.1
  · intro h
    refine ⟨?_, ?_, h.1⟩
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (by rw [coprime_comm]; exact h.2.coprime_dvd_right hkd)
        (dvd_of_mem_divisors hk) (dvd_of_mem_divisors hm)
    · exact main4EqGcdMulOfDvdOfCoprime hkd h.2
        (by rintro rfl; simp at hk)

/-- Positivity comparison used to prove the optimal base weights are at
most one in magnitude. -/
theorem main4SelbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * (μ d : ℝ) * S := by
  calc
    S = ∑ k ∈ divisors P, ∑ l ∈ divisors P,
        if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ y then g l else 0 := by
      unfold main4SelbergBoundingSum
      dsimp only
      rw [sum_comm]
      apply sum_congr rfl
      intro l _hl
      simp_rw [ite_and]
      rw [sum_ite_eq_of_mem']
      rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans hdP,
        s.toBoundingSieve.prodPrimes_ne_zero⟩
    _ = ∑ k ∈ divisors P,
        if k ∣ d then
          g k * ∑ m ∈ divisors P,
            if ((k * m : ℕ) : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
        else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [mul_sum]
      by_cases hkd : k ∣ d
      swap
      · rw [if_neg hkd, sum_eq_zero]
        intro l _hl
        rw [if_neg]
        intro h
        rw [h.1] at hkd
        exact hkd (Nat.gcd_dvd_left d l)
      rw [if_pos hkd, main4SumMulSubst k P]
      · apply sum_congr rfl
        intro m hm
        rw [mul_ite_zero, ← ite_and]
        apply if_ctx_congr _ _ (fun _ ↦ rfl)
        · exact main4SelbergGcdProductIff s hkd hk hm
        · intro h
          exact s.toBoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime
            (by
              rw [gcd_comm]
              exact h.2.coprime_dvd_right hkd)
      · intro l _hl hkl
        rw [if_neg]
        intro h
        rw [h.1] at hkl
        exact hkl (Nat.gcd_dvd_right d l)
    _ ≥ ∑ k ∈ divisors P,
        if k ∣ d then
          g k * ∑ m ∈ divisors P,
            if ((d * m : ℕ) : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
        else 0 := by
      apply sum_le_sum
      intro k hk
      by_cases hkd : k ∣ d
      swap
      · rw [if_neg hkd, if_neg hkd]
      rw [if_pos hkd, if_pos hkd]
      apply mul_le_mul le_rfl _ _
        (le_of_lt (s.toBoundingSieve.selbergTerms_pos (hkd.trans hdP)))
      · apply sum_le_sum
        intro m hm
        split_ifs with h h' h'
        · rfl
        · exfalso
          apply h'
          refine ⟨?_, h.2⟩
          trans (((d * m : ℕ) : ℝ) ^ 2)
          · norm_cast
            gcongr
            exact Nat.le_of_dvd
              (Nat.pos_of_ne_zero
                (ne_zero_of_dvd_ne_zero
                  s.toBoundingSieve.prodPrimes_ne_zero hdP)) hkd
          · exact h.1
        · exact le_of_lt (s.toBoundingSieve.selbergTerms_pos
            (dvd_of_mem_divisors hm))
        · rfl
      · apply sum_nonneg
        intro m hm
        split_ifs
        · exact le_of_lt (s.toBoundingSieve.selbergTerms_pos
            (dvd_of_mem_divisors hm))
        · rfl
    _ = γ d * (μ d : ℝ) * S := by
      simp_rw [← ite_zero_mul]
      rw [← sum_mul,
        s.toBoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
      trans S * S⁻¹ * (μ d : ℝ) ^ 2 * (ν d)⁻¹ * g d *
          (∑ m ∈ divisors P,
            if ((d * m : ℕ) : ℝ) ^ 2 ≤ y ∧ m.Coprime d then g m else 0)
      · rw [mul_inv_cancel₀ (main4SelbergBoundingSum_ne_zero s)]
        have hmu : (μ d : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (s.toBoundingSieve.prodPrimes_squarefree.squarefree_of_dvd hdP)
        rw [hmu]
        ring
      · unfold main4SelbergWeights
        dsimp only
        rw [if_pos hdP]
        ring

/-- Every cutoff-optimal base weight has absolute value at most one. -/
theorem main4SelbergWeights_abs_le_one (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [main4SelbergWeights_eq_zero_of_not_dvd s hdP]
    simp
  have hmul : γ d * (μ d : ℝ) * S ≤ 1 * S := by
    rw [one_mul]
    exact main4SelbergBoundingSum_ge s hdP
  have hscaled : γ d * (μ d : ℝ) ≤ 1 := by
    exact le_of_mul_le_mul_of_pos_right hmul
      (main4SelbergBoundingSum_pos s)
  convert hscaled using 1
  rw [← abs_of_nonneg (main4SelbergWeights_mul_mu_nonneg s d hdP),
    abs_mul, ← Int.cast_abs,
    ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.toBoundingSieve.prodPrimes_squarefree.squarefree_of_dvd hdP),
    Int.cast_one, mul_one]

/-- The short Selberg upper coefficients have the standard
`3 ^ omega(d)` coefficient bound. -/
theorem main4SelbergMuPlus_abs_le_three_pow_omega
    (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3 : ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z ↦ if n = x.lcm z then 1 else 0
  unfold main4SelbergMuPlus BoundingSieve.lambdaSquared
  calc
    |∑ d₁ ∈ n.divisors, ∑ d₂ ∈ n.divisors,
        if n = d₁.lcm d₂ then γ d₁ * γ d₂ else 0| ≤
        ∑ d₁ ∈ n.divisors,
          |∑ d₂ ∈ n.divisors,
            if n = d₁.lcm d₂ then γ d₁ * γ d₂ else 0| := by
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ d₁ ∈ n.divisors, ∑ d₂ ∈ n.divisors,
        |if n = d₁.lcm d₂ then γ d₁ * γ d₂ else 0| := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ d₁ ∈ n.divisors, ∑ d₂ ∈ n.divisors, f d₁ d₂ := by
      gcongr with d₁ _hd₁ d₂ _hd₂
      rw [apply_ite abs, abs_zero, abs_mul]
      simp only [f]
      by_cases h : n = d₁.lcm d₂
      · rw [if_pos h, if_pos h]
        exact mul_le_one₀ (main4SelbergWeights_abs_le_one s d₁)
          (abs_nonneg (γ d₂)) (main4SelbergWeights_abs_le_one s d₂)
      · rw [if_neg h, if_neg h]
    _ = (n.divisors ×ˢ n.divisors).sum (fun p ↦ f p.1 p.2) := by
      rw [← Finset.sum_product']
    _ = ((n.divisors ×ˢ n.divisors).filter
        (fun p : ℕ × ℕ ↦ n = p.1.lcm p.2)).card := by
      unfold f
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      simp
    _ = (3 : ℕ) ^ ω n := by
      norm_cast
      simpa [eq_comm] using Nat.card_pair_lcm_eq
        (s.toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hn)
    _ = (3 : ℝ) ^ ω n := by norm_num

/-- A deliberately crude polynomial form of the coefficient bound.  It is
often enough for Wilson's `M ^ epsilon` error term after choosing a smaller
sieve level, and avoids any average-order theorem for `3 ^ omega`. -/
theorem main4ThreePowOmega_le_sq (n : ℕ) (hn : 0 < n) :
    3 ^ ω n ≤ n ^ 2 := by
  have hcard : n.primeFactors.card = ω n := by
    rw [ArithmeticFunction.cardDistinctFactors_apply,
      ← Nat.toFinset_factors, List.card_toFinset]
  have htwo : 2 ^ ω n ≤ n := by
    calc
      2 ^ ω n = ∏ _p ∈ n.primeFactors, 2 := by
        rw [Finset.prod_const, hcard]
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_le_prod
        · intro
          omega
        · intro p hp
          exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  calc
    3 ^ ω n ≤ 4 ^ ω n := Nat.pow_le_pow_left (by omega) _
    _ = (2 ^ ω n) ^ 2 := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ n ^ 2 := Nat.pow_le_pow_left htwo _

theorem main4SelbergMuPlus_abs_le_sq
    (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (n : ℝ) ^ 2 := by
  calc
    |μ⁺ n| ≤ (3 : ℝ) ^ ω n :=
      main4SelbergMuPlus_abs_le_three_pow_omega s n hn
    _ ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast main4ThreePowOmega_le_sq n
        (Nat.pos_of_mem_divisors hn)

end SelbergOptimizer

end

end PellPaper
