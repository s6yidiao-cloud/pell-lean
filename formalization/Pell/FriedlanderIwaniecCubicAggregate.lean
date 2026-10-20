import Pell.TauThreeBounds
import Pell.JacobiPrefixCancellation

/-!
# Cubic aggregation in the Friedlander--Iwaniec bilinear estimate

This file formalizes the exact finite regrouping used at the start of
Section 9 in Friedlander--Iwaniec's proof of their bilinear Jacobi-symbol
estimate.  Cubing the inner `m`-sum produces ordered triples
`(m₁,m₂,m₃)`.  Regrouping those triples by
`ℓ = m₁ m₂ m₃` gives a coefficient whose norm is at most
`tauThree ℓ`.

No external analytic premise is assumed here, and no character-sum bound is
proved in this module.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The coefficient obtained by collecting the cubic expansion over
ordered triples in `[1,A]³` with product `ell`. -/
def friedlanderIwaniecCubicCoefficient
    (A ell : ℕ) (alpha : ℕ → ℂ) : ℂ :=
  ∑ t ∈ positiveOrderedTripleFactorFibreUpTo A ell,
    alpha t.1 * alpha t.2.1 * alpha t.2.2

/-- The exact three-variable `tauThree` aggregate appearing after Cauchy's
inequality in Friedlander--Iwaniec, Section 9. -/
def friedlanderIwaniecTripleTauMass (A : ℕ) : ℝ :=
  ∑ m₁ ∈ Finset.Icc 1 A,
    ∑ m₂ ∈ Finset.Icc 1 A,
      ∑ m₃ ∈ Finset.Icc 1 A,
        (tauThree (m₁ * m₂ * m₃) : ℝ)

/-- The elementary `M³ (1 + log M)⁶` bound for the three-variable
`tauThree` aggregate.  This is the explicit uniform version of the
`M³ (log 2M)⁶` factor on p. 112 of Friedlander--Iwaniec. -/
theorem friedlanderIwaniecTripleTauMass_le
    (A : ℕ) :
    friedlanderIwaniecTripleTauMass A ≤
      (A : ℝ) ^ 3 * (1 + Real.log (A : ℝ)) ^ 6 := by
  have hsum :
      (∑ m ∈ Finset.Icc 1 A, (tauThree m : ℝ)) ≤
        (A : ℝ) * (1 + Real.log (A : ℝ)) ^ 2 := by
    have h := sum_Ioc_tauThree_cast_le_mul_one_add_log_sq A
    rw [Nat.cast_sum] at h
    have hrange : Finset.Ioc 0 A = Finset.Icc 1 A := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    simpa only [hrange] using h
  have hsumNonneg :
      0 ≤ ∑ m ∈ Finset.Icc 1 A, (tauThree m : ℝ) := by
    positivity
  unfold friedlanderIwaniecTripleTauMass
  calc
    ∑ m₁ ∈ Finset.Icc 1 A,
        ∑ m₂ ∈ Finset.Icc 1 A,
          ∑ m₃ ∈ Finset.Icc 1 A,
            (tauThree (m₁ * m₂ * m₃) : ℝ) ≤
        ∑ m₁ ∈ Finset.Icc 1 A,
          ∑ m₂ ∈ Finset.Icc 1 A,
            ∑ m₃ ∈ Finset.Icc 1 A,
              ((tauThree m₁ * tauThree m₂ * tauThree m₃ : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro m₁ _hm₁
      apply Finset.sum_le_sum
      intro m₂ _hm₂
      apply Finset.sum_le_sum
      intro m₃ _hm₃
      exact_mod_cast tauThree_mul_mul_le m₁ m₂ m₃
    _ = (∑ m ∈ Finset.Icc 1 A, (tauThree m : ℝ)) ^ 3 := by
      rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m₁ _hm₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m₂ _hm₂
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m₃ _hm₃
      push_cast
      ring
    _ ≤ ((A : ℝ) * (1 + Real.log (A : ℝ)) ^ 2) ^ 3 :=
      pow_le_pow_left₀ hsumNonneg hsum 3
    _ = (A : ℝ) ^ 3 * (1 + Real.log (A : ℝ)) ^ 6 := by ring

/-- The triangle-inequality bound for one product fibre. -/
theorem norm_friedlanderIwaniecCubicCoefficient_le_card_fibre
    (A ell : ℕ) (alpha : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ≤
      ((positiveOrderedTripleFactorFibreUpTo A ell).card : ℝ) := by
  classical
  unfold friedlanderIwaniecCubicCoefficient
  calc
    ‖∑ t ∈ positiveOrderedTripleFactorFibreUpTo A ell,
        alpha t.1 * alpha t.2.1 * alpha t.2.2‖ ≤
        ∑ t ∈ positiveOrderedTripleFactorFibreUpTo A ell,
          ‖alpha t.1 * alpha t.2.1 * alpha t.2.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _t ∈ positiveOrderedTripleFactorFibreUpTo A ell, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨htBox, _htProd⟩ := Finset.mem_filter.mp ht
      obtain ⟨h₁, h₂₃⟩ := Finset.mem_product.mp htBox
      obtain ⟨h₂, h₃⟩ := Finset.mem_product.mp h₂₃
      rw [norm_mul, norm_mul]
      exact mul_le_one₀
        (mul_le_one₀ (halpha t.1 h₁) (norm_nonneg _)
          (halpha t.2.1 h₂))
        (norm_nonneg _) (halpha t.2.2 h₃)
    _ = ((positiveOrderedTripleFactorFibreUpTo A ell).card : ℝ) := by simp

/-- If the original coefficients have norm at most one in `[1,A]`, the
coefficient of product `ell` in their cubic expansion has norm at most
`tauThree ell`. -/
theorem norm_friedlanderIwaniecCubicCoefficient_le_tauThree
    (A ell : ℕ) (alpha : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ≤
      (tauThree ell : ℝ) := by
  exact (norm_friedlanderIwaniecCubicCoefficient_le_card_fibre
      A ell alpha halpha).trans (by
        exact_mod_cast card_positiveOrderedTripleFactorFibreUpTo_le_tauThree A ell)

/-- The total mass of the regrouped cubic coefficients is at most the
number `A³` of ordered triples in the original box. -/
theorem sum_norm_friedlanderIwaniecCubicCoefficient_le_cube
    (A : ℕ) (alpha : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    (∑ ell ∈ Finset.Icc 1 (A ^ 3),
        ‖friedlanderIwaniecCubicCoefficient A ell alpha‖) ≤
      (A : ℝ) ^ 3 := by
  classical
  let I := Finset.Icc 1 A
  let T := I.product (I.product I)
  let prod : ℕ × ℕ × ℕ → ℕ := fun t ↦ t.1 * t.2.1 * t.2.2
  have hmaps : ∀ t ∈ T, prod t ∈ Finset.Icc 1 (A ^ 3) := by
    intro t ht
    obtain ⟨h₁, h₂₃⟩ := Finset.mem_product.mp ht
    obtain ⟨h₂, h₃⟩ := Finset.mem_product.mp h₂₃
    obtain ⟨h₁pos, h₁A⟩ := Finset.mem_Icc.mp h₁
    obtain ⟨h₂pos, h₂A⟩ := Finset.mem_Icc.mp h₂
    obtain ⟨h₃pos, h₃A⟩ := Finset.mem_Icc.mp h₃
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.mul_pos (Nat.mul_pos h₁pos h₂pos) h₃pos
    · dsimp only [prod]
      simpa only [pow_three, mul_assoc] using
        Nat.mul_le_mul (Nat.mul_le_mul h₁A h₂A) h₃A
  calc
    ∑ ell ∈ Finset.Icc 1 (A ^ 3),
        ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ≤
        ∑ ell ∈ Finset.Icc 1 (A ^ 3),
          ((positiveOrderedTripleFactorFibreUpTo A ell).card : ℝ) := by
      apply Finset.sum_le_sum
      intro ell _hell
      exact norm_friedlanderIwaniecCubicCoefficient_le_card_fibre
        A ell alpha halpha
    _ = ((T.card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]
      norm_cast
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      rfl
    _ = (A : ℝ) ^ 3 := by
      simp [T, I, pow_three]

/-- The squared `L²` mass of the collected coefficients is bounded by the
source's three-variable `tauThree` factor.  This is the precise coefficient
estimate used in the Cauchy step on p. 112. -/
theorem sum_norm_friedlanderIwaniecCubicCoefficient_sq_le_tripleTauMass
    (A : ℕ) (alpha : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    (∑ ell ∈ Finset.Icc 1 (A ^ 3),
        ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ^ 2) ≤
      friedlanderIwaniecTripleTauMass A := by
  classical
  let I := Finset.Icc 1 A
  let T := I.product (I.product I)
  let prod : ℕ × ℕ × ℕ → ℕ := fun t ↦ t.1 * t.2.1 * t.2.2
  have hmaps : ∀ t ∈ T, prod t ∈ Finset.Icc 1 (A ^ 3) := by
    intro t ht
    obtain ⟨h₁, h₂₃⟩ := Finset.mem_product.mp ht
    obtain ⟨h₂, h₃⟩ := Finset.mem_product.mp h₂₃
    obtain ⟨h₁pos, h₁A⟩ := Finset.mem_Icc.mp h₁
    obtain ⟨h₂pos, h₂A⟩ := Finset.mem_Icc.mp h₂
    obtain ⟨h₃pos, h₃A⟩ := Finset.mem_Icc.mp h₃
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.mul_pos (Nat.mul_pos h₁pos h₂pos) h₃pos
    · dsimp only [prod]
      simpa only [pow_three, mul_assoc] using
        Nat.mul_le_mul (Nat.mul_le_mul h₁A h₂A) h₃A
  have hpoint (ell : ℕ) :
      ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ^ 2 ≤
        ((positiveOrderedTripleFactorFibreUpTo A ell).card : ℝ) *
          (tauThree ell : ℝ) := by
    let r : ℝ := (positiveOrderedTripleFactorFibreUpTo A ell).card
    have hnorm : ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ≤ r :=
      norm_friedlanderIwaniecCubicCoefficient_le_card_fibre
        A ell alpha halpha
    have hrtau : r ≤ (tauThree ell : ℝ) := by
      dsimp only [r]
      exact_mod_cast card_positiveOrderedTripleFactorFibreUpTo_le_tauThree A ell
    calc
      ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ^ 2 ≤ r ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ r * (tauThree ell : ℝ) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hrtau (by positivity)
  calc
    ∑ ell ∈ Finset.Icc 1 (A ^ 3),
        ‖friedlanderIwaniecCubicCoefficient A ell alpha‖ ^ 2 ≤
        ∑ ell ∈ Finset.Icc 1 (A ^ 3),
          ((positiveOrderedTripleFactorFibreUpTo A ell).card : ℝ) *
            (tauThree ell : ℝ) := by
      exact Finset.sum_le_sum fun ell _hell ↦ hpoint ell
    _ = ∑ ell ∈ Finset.Icc 1 (A ^ 3),
          ∑ t ∈ T with prod t = ell, (tauThree ell : ℝ) := by
      apply Finset.sum_congr rfl
      intro ell _hell
      simp [positiveOrderedTripleFactorFibreUpTo, T, I, prod]
    _ = ∑ t ∈ T, (tauThree (prod t) : ℝ) :=
      Finset.sum_fiberwise_of_maps_to' hmaps fun ell ↦ (tauThree ell : ℝ)
    _ = friedlanderIwaniecTripleTauMass A := by
      simp [friedlanderIwaniecTripleTauMass, T, I, prod,
        Finset.product_eq_sprod, Finset.sum_product]

/-- Cauchy's inequality in the exact finite form used in the source: the
unknown cubic coefficients disappear into the three-variable `tauThree`
mass, and the remaining factor is an unweighted product-variable moment.
-/
theorem norm_sum_friedlanderIwaniecCubicCoefficient_mul_sq_le_tripleTauMass
    (A : ℕ) (alpha F : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    ‖∑ ell ∈ Finset.Icc 1 (A ^ 3),
        friedlanderIwaniecCubicCoefficient A ell alpha * F ell‖ ^ 2 ≤
      friedlanderIwaniecTripleTauMass A *
        ∑ ell ∈ Finset.Icc 1 (A ^ 3), ‖F ell‖ ^ 2 := by
  let S := Finset.Icc 1 (A ^ 3)
  let c : ℕ → ℂ := fun ell ↦
    friedlanderIwaniecCubicCoefficient A ell alpha
  have htriangle :
      ‖∑ ell ∈ S, c ell * F ell‖ ≤
        ∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ := by
    calc
      ‖∑ ell ∈ S, c ell * F ell‖ ≤
          ∑ ell ∈ S, ‖c ell * F ell‖ := norm_sum_le _ _
      _ = ∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ := by
        simp only [norm_mul]
  have hcauchy :
      (∑ ell ∈ S, ‖c ell‖ * ‖F ell‖) ^ 2 ≤
        (∑ ell ∈ S, ‖c ell‖ ^ 2) *
          ∑ ell ∈ S, ‖F ell‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S (fun ell ↦ ‖c ell‖) (fun ell ↦ ‖F ell‖)
  have hcoeff :
      (∑ ell ∈ S, ‖c ell‖ ^ 2) ≤
        friedlanderIwaniecTripleTauMass A :=
    sum_norm_friedlanderIwaniecCubicCoefficient_sq_le_tripleTauMass
      A alpha halpha
  change ‖∑ ell ∈ S, c ell * F ell‖ ^ 2 ≤ _
  calc
    ‖∑ ell ∈ S, c ell * F ell‖ ^ 2 ≤
        (∑ ell ∈ S, ‖c ell‖ * ‖F ell‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ ell ∈ S, ‖c ell‖ ^ 2) *
        ∑ ell ∈ S, ‖F ell‖ ^ 2 := hcauchy
    _ ≤ friedlanderIwaniecTripleTauMass A *
        ∑ ell ∈ S, ‖F ell‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- Explicit uniform consequence of the source's Cauchy step and the
elementary triple-`tauThree` aggregate estimate. -/
theorem norm_sum_friedlanderIwaniecCubicCoefficient_mul_sq_le_cube_log
    (A : ℕ) (alpha F : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    ‖∑ ell ∈ Finset.Icc 1 (A ^ 3),
        friedlanderIwaniecCubicCoefficient A ell alpha * F ell‖ ^ 2 ≤
      (A : ℝ) ^ 3 * (1 + Real.log (A : ℝ)) ^ 6 *
        ∑ ell ∈ Finset.Icc 1 (A ^ 3), ‖F ell‖ ^ 2 := by
  exact (norm_sum_friedlanderIwaniecCubicCoefficient_mul_sq_le_tripleTauMass
    A alpha F halpha).trans
      (mul_le_mul_of_nonneg_right (friedlanderIwaniecTripleTauMass_le A)
        (by positivity))

/-- A complementary weighted form of Cauchy's inequality: the first factor
costs only the original box size `A³`, while the second factor carries the
explicit weight `tauThree ell`. -/
theorem norm_sum_friedlanderIwaniecCubicCoefficient_mul_sq_le
    (A : ℕ) (alpha F : ℕ → ℂ)
    (halpha : ∀ m ∈ Finset.Icc 1 A, ‖alpha m‖ ≤ 1) :
    ‖∑ ell ∈ Finset.Icc 1 (A ^ 3),
        friedlanderIwaniecCubicCoefficient A ell alpha * F ell‖ ^ 2 ≤
      (A : ℝ) ^ 3 *
        ∑ ell ∈ Finset.Icc 1 (A ^ 3),
          (tauThree ell : ℝ) * ‖F ell‖ ^ 2 := by
  classical
  let S := Finset.Icc 1 (A ^ 3)
  let c : ℕ → ℂ := fun ell ↦
    friedlanderIwaniecCubicCoefficient A ell alpha
  have htriangle :
      ‖∑ ell ∈ S, c ell * F ell‖ ≤
        ∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ := by
    calc
      ‖∑ ell ∈ S, c ell * F ell‖ ≤
          ∑ ell ∈ S, ‖c ell * F ell‖ := norm_sum_le _ _
      _ = ∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ := by
        simp only [norm_mul]
  have hcauchy :
      (∑ ell ∈ S, ‖c ell‖ * ‖F ell‖) ^ 2 ≤
        (∑ ell ∈ S, ‖c ell‖) *
          ∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro ell _hell
      exact norm_nonneg _
    · intro ell _hell
      exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
    · intro ell _hell
      ring_nf
      exact le_rfl
  have hmass : (∑ ell ∈ S, ‖c ell‖) ≤ (A : ℝ) ^ 3 := by
    exact sum_norm_friedlanderIwaniecCubicCoefficient_le_cube A alpha halpha
  have hweighted :
      (∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ ^ 2) ≤
        ∑ ell ∈ S, (tauThree ell : ℝ) * ‖F ell‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro ell _hell
    exact mul_le_mul_of_nonneg_right
      (norm_friedlanderIwaniecCubicCoefficient_le_tauThree
        A ell alpha halpha) (sq_nonneg _)
  change ‖∑ ell ∈ S, c ell * F ell‖ ^ 2 ≤ _
  calc
    ‖∑ ell ∈ S, c ell * F ell‖ ^ 2 ≤
        (∑ ell ∈ S, ‖c ell‖ * ‖F ell‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ ell ∈ S, ‖c ell‖) *
        ∑ ell ∈ S, ‖c ell‖ * ‖F ell‖ ^ 2 := hcauchy
    _ ≤ (A : ℝ) ^ 3 *
        ∑ ell ∈ S, (tauThree ell : ℝ) * ‖F ell‖ ^ 2 := by
      exact mul_le_mul hmass hweighted
        (Finset.sum_nonneg fun _ _ ↦
          mul_nonneg (by positivity) (sq_nonneg _)) (by positivity)

/-- Exact product-fibre regrouping of the cube of a finite sum.  The only
property required of `chi` is multiplicativity; the Jacobi-symbol instance
is supplied below. -/
theorem pow_three_sum_mul_eq_sum_friedlanderIwaniecCubicCoefficient_mul
    (A : ℕ) (alpha chi : ℕ → ℂ)
    (hchi : ∀ a b : ℕ, chi (a * b) = chi a * chi b) :
    (∑ m ∈ Finset.Icc 1 A, alpha m * chi m) ^ 3 =
      ∑ ell ∈ Finset.Icc 1 (A ^ 3),
        friedlanderIwaniecCubicCoefficient A ell alpha * chi ell := by
  classical
  let I := Finset.Icc 1 A
  let T := I.product (I.product I)
  let prod : ℕ × ℕ × ℕ → ℕ := fun t ↦ t.1 * t.2.1 * t.2.2
  let coeff : ℕ × ℕ × ℕ → ℂ := fun t ↦
    alpha t.1 * alpha t.2.1 * alpha t.2.2
  have hmaps : ∀ t ∈ T, prod t ∈ Finset.Icc 1 (A ^ 3) := by
    intro t ht
    obtain ⟨h₁, h₂₃⟩ := Finset.mem_product.mp ht
    obtain ⟨h₂, h₃⟩ := Finset.mem_product.mp h₂₃
    obtain ⟨h₁pos, h₁A⟩ := Finset.mem_Icc.mp h₁
    obtain ⟨h₂pos, h₂A⟩ := Finset.mem_Icc.mp h₂
    obtain ⟨h₃pos, h₃A⟩ := Finset.mem_Icc.mp h₃
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.mul_pos (Nat.mul_pos h₁pos h₂pos) h₃pos
    · dsimp only [prod]
      simpa only [pow_three, mul_assoc] using
        Nat.mul_le_mul (Nat.mul_le_mul h₁A h₂A) h₃A
  have hgroup :
      ∑ ell ∈ Finset.Icc 1 (A ^ 3),
          friedlanderIwaniecCubicCoefficient A ell alpha * chi ell =
        ∑ t ∈ T, coeff t * chi (prod t) := by
    calc
      ∑ ell ∈ Finset.Icc 1 (A ^ 3),
          friedlanderIwaniecCubicCoefficient A ell alpha * chi ell =
          ∑ ell ∈ Finset.Icc 1 (A ^ 3),
            ∑ t ∈ T with prod t = ell, coeff t * chi ell := by
        apply Finset.sum_congr rfl
        intro ell _hell
        rw [friedlanderIwaniecCubicCoefficient, Finset.sum_mul]
        rfl
      _ = ∑ ell ∈ Finset.Icc 1 (A ^ 3),
            ∑ t ∈ T with prod t = ell, coeff t * chi (prod t) := by
        apply Finset.sum_congr rfl
        intro ell _hell
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = ∑ t ∈ T, coeff t * chi (prod t) :=
        Finset.sum_fiberwise_of_maps_to hmaps (fun t ↦ coeff t * chi (prod t))
  rw [hgroup]
  simp only [T, I, coeff, prod, Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [hchi]
  rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  ring

/-- Source-shaped specialization of the product-fibre regrouping to the
Jacobi symbol.  This is the exact identity behind the triple `m`-sum in
Section 9 of the Friedlander--Iwaniec argument. -/
theorem pow_three_sum_alpha_mul_jacobi_eq_cubicAggregate
    (A n : ℕ) (alpha : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 A,
        alpha m * (jacobiSym (m : ℤ) n : ℂ)) ^ 3 =
      ∑ ell ∈ Finset.Icc 1 (A ^ 3),
        friedlanderIwaniecCubicCoefficient A ell alpha *
          (jacobiSym (ell : ℤ) n : ℂ) := by
  apply pow_three_sum_mul_eq_sum_friedlanderIwaniecCubicCoefficient_mul
  intro a b
  norm_cast
  simpa using jacobiSym.mul_left (a : ℤ) (b : ℤ) n

end

end PellPaper
