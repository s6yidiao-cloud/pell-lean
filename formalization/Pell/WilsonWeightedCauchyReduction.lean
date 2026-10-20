import Pell.CorollaryOddClassMain4WilsonPublishedInputs
import Pell.SquareProductPairCount

/-!
# Wilson's weighted Cauchy and square--nonsquare reduction

This module formalizes the first finite part of the proof of Theorem 1.1 in
Cameron Wilson, *An improved large sieve for quadratic characters via Hooley
neutralisers* (Section 2).  It proves the weighted Cauchy inequality and the
monotonicity step through which a Hooley neutraliser majorizes the resulting
nonnegative second moment.  It then expands the majorant and partitions it
according to whether the product of the two numerator variables is a square.

The Hooley-neutraliser estimates for the two resulting correlations are not
asserted here.  Thus this file reduces the remaining analytic frontier but
does not claim Wilson's theorem.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The inner Jacobi-symbol sum in Wilson's quadratic rectangle. -/
def wilsonJacobiInner (a : ℕ → ℝ) (N m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (jacobiSym (n : ℤ) m : ℝ)

/-- The nonnegative mass occurring in weighted Cauchy--Schwarz. -/
def wilsonWeightedMass (b f : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, |b m| * f m

/-- The weighted Jacobi second moment after Cauchy--Schwarz. -/
def wilsonWeightedSecondMoment
    (a w : ℕ → ℝ) (M N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, w m * (wilsonJacobiInner a N m) ^ 2

/-- The denominator-variable correlation attached to one numerator product. -/
def wilsonJacobiCorrelation
    (w : ℕ → ℝ) (M q : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, w m * (jacobiSym (q : ℤ) m : ℝ)

/-- Wilson's first Cauchy--Schwarz step, for an arbitrary nonnegative
multiplicative-variable weight. -/
theorem abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le
    (a b f : ℕ → ℝ) (M N : ℕ)
    (hf : ∀ m ∈ Finset.Icc 1 M, 0 ≤ f m) :
    |main4OrdinaryJacobiRectangle a (fun m ↦ b m * f m) M N| ^ 2 ≤
      wilsonWeightedMass b f M *
        wilsonWeightedSecondMoment a (fun m ↦ |b m| * f m) M N := by
  unfold main4OrdinaryJacobiRectangle wilsonWeightedMass
    wilsonWeightedSecondMoment wilsonJacobiInner
  rw [sq_abs]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro m hm
    exact mul_nonneg (abs_nonneg _) (hf m hm)
  · intro m hm
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (hf m hm)) (sq_nonneg _)
  · intro m hm
    dsimp only
    calc
      (b m * f m *
          (∑ n ∈ Finset.Icc 1 N,
            a n * (jacobiSym (n : ℤ) m : ℝ))) ^ 2 =
          (b m) ^ 2 * (f m) ^ 2 *
            (∑ n ∈ Finset.Icc 1 N,
              a n * (jacobiSym (n : ℤ) m : ℝ)) ^ 2 := by ring
      _ = |b m| ^ 2 * (f m) ^ 2 *
            (∑ n ∈ Finset.Icc 1 N,
              a n * (jacobiSym (n : ℤ) m : ℝ)) ^ 2 := by rw [sq_abs]
      _ = |b m| * f m *
          (|b m| * f m *
            (∑ n ∈ Finset.Icc 1 N,
              a n * (jacobiSym (n : ℤ) m : ℝ)) ^ 2) := by ring
      _ ≤ |b m| * f m *
          (|b m| * f m *
            (∑ n ∈ Finset.Icc 1 N,
              a n * (jacobiSym (n : ℤ) m : ℝ)) ^ 2) := le_rfl

/-- The preceding Cauchy inequality at Wilson's exact weight
`f(m) = 1 / tau(m)`. -/
theorem abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le
    (a b : ℕ → ℝ) (M N : ℕ) :
    |main4OrdinaryJacobiRectangle a
        (fun m ↦ b m * main4WilsonReciprocalDivisorWeight m) M N| ^ 2 ≤
      wilsonWeightedMass b main4WilsonReciprocalDivisorWeight M *
        wilsonWeightedSecondMoment a
          (fun m ↦ |b m| * main4WilsonReciprocalDivisorWeight m) M N := by
  exact abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le
    a b main4WilsonReciprocalDivisorWeight M N
      (fun m _hm ↦ main4WilsonReciprocalDivisorWeight_nonneg m)

/-- A coefficient sequence bounded by one contributes no more mass than the
bare nonnegative weight. -/
theorem wilsonWeightedMass_le_sum_weight
    (b f : ℕ → ℝ) (M : ℕ)
    (hb : ∀ m : ℕ, |b m| ≤ 1)
    (hf : ∀ m : ℕ, 0 ≤ f m) :
    wilsonWeightedMass b f M ≤ ∑ m ∈ Finset.Icc 1 M, f m := by
  unfold wilsonWeightedMass
  apply Finset.sum_le_sum
  intro m _hm
  simpa using mul_le_mul_of_nonneg_right (hb m) (hf m)

/-- A pointwise majorant for the denominator weight majorizes the complete
nonnegative quadratic moment.  In Wilson's proof this is applied *before*
expanding the square: `w(m) = |b m| f(m)` and the upper weight is the Hooley
neutraliser supplied by Lemma 2.1. -/
theorem wilsonWeightedSecondMoment_mono
    (a w W : ℕ → ℝ) (M N : ℕ)
    (hwW : ∀ m ∈ Finset.Icc 1 M, w m ≤ W m) :
    wilsonWeightedSecondMoment a w M N ≤
      wilsonWeightedSecondMoment a W M N := by
  unfold wilsonWeightedSecondMoment
  apply Finset.sum_le_sum
  intro m hm
  exact mul_le_mul_of_nonneg_right (hwW m hm) (sq_nonneg _)

/-- Exact expansion of Wilson's weighted second moment into correlations in
the denominator variable. -/
theorem wilsonWeightedSecondMoment_eq_sum_pair_correlation
    (a w : ℕ → ℝ) (M N : ℕ) :
    wilsonWeightedSecondMoment a w M N =
      ∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2) := by
  classical
  let I := Finset.Icc 1 M
  let J := Finset.Icc 1 N
  let P := J.product J
  have hexpand (m : ℕ) :
      (wilsonJacobiInner a N m) ^ 2 =
        ∑ p ∈ P,
          a p.1 * a p.2 *
            (jacobiSym ((p.1 * p.2 : ℕ) : ℤ) m : ℝ) := by
    rw [wilsonJacobiInner, pow_two, Finset.sum_mul_sum]
    rw [show P = J.product J from rfl, Finset.product_eq_sprod,
      Finset.sum_product]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    rw [show ((n * k : ℕ) : ℤ) = (n : ℤ) * (k : ℤ) by norm_num,
      jacobiSym.mul_left, Int.cast_mul]
    ring
  unfold wilsonWeightedSecondMoment
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  change
    (∑ p ∈ P, ∑ m ∈ I,
      w m *
        (a p.1 * a p.2 *
          (jacobiSym ((p.1 * p.2 : ℕ) : ℤ) m : ℝ))) = _
  apply Finset.sum_congr rfl
  intro p hp
  unfold wilsonJacobiCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Exact partition of the expanded moment into the square diagonal and the
nonsquare correlations. -/
theorem wilsonWeightedSecondMoment_eq_square_add_nonsquare
    (a w : ℕ → ℝ) (M N : ℕ) :
    wilsonWeightedSecondMoment a w M N =
      ∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2) +
      ∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ ¬ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2) := by
  classical
  rw [wilsonWeightedSecondMoment_eq_sum_pair_correlation]
  exact (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).product (Finset.Icc 1 N))
    (fun p ↦ IsSquare (p.1 * p.2))
    (fun p ↦ a p.1 * a p.2 *
      wilsonJacobiCorrelation w M (p.1 * p.2))).symm

/-- Once the square and nonsquare contributions for an already chosen weight
are bounded, their sum controls its full weighted second moment.  This theorem
is deliberately agnostic about how those two analytic bounds are proved. -/
theorem wilsonWeightedSecondMoment_le_of_square_nonsquare_bounds
    (a w : ℕ → ℝ) (M N : ℕ) (Ds Ens : ℝ)
    (hsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2)| ≤ Ds)
    (hnonsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ ¬ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2)| ≤ Ens) :
    wilsonWeightedSecondMoment a w M N ≤ Ds + Ens := by
  rw [wilsonWeightedSecondMoment_eq_square_add_nonsquare]
  calc
    _ ≤
        |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
            (fun p ↦ IsSquare (p.1 * p.2)),
          a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2)| +
        |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
            (fun p ↦ ¬ IsSquare (p.1 * p.2)),
          a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2)| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ Ds + Ens := add_le_add hsquare hnonsquare

/-- A pointwise version of the square--nonsquare handoff.  The elementary
square-product count supplies the factor `N (1 + log N)`; all `N^2` ordered
pairs are allowed in the nonsquare error. -/
theorem wilsonWeightedSecondMoment_le_of_pairwise_correlation_bounds
    (a w : ℕ → ℝ) (M N : ℕ) (D E : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ha : ∀ n : ℕ, |a n| ≤ 1)
    (hsquare : ∀ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      IsSquare (p.1 * p.2) →
        |wilsonJacobiCorrelation w M (p.1 * p.2)| ≤ D)
    (hnonsquare : ∀ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      ¬ IsSquare (p.1 * p.2) →
        |wilsonJacobiCorrelation w M (p.1 * p.2)| ≤ E) :
    wilsonWeightedSecondMoment a w M N ≤
      D * ((N : ℝ) * (1 + Real.log (N : ℝ))) + E * (N : ℝ) ^ 2 := by
  classical
  let P := (Finset.Icc 1 N).product (Finset.Icc 1 N)
  have hpoint (p : ℕ × ℕ) (hp : p ∈ P) :
      a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2) ≤
        (if IsSquare (p.1 * p.2) then D else 0) + E := by
    have habs :
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2) ≤
          |wilsonJacobiCorrelation w M (p.1 * p.2)| := by
      calc
        a p.1 * a p.2 * wilsonJacobiCorrelation w M (p.1 * p.2) ≤
            |a p.1 * a p.2 *
              wilsonJacobiCorrelation w M (p.1 * p.2)| := le_abs_self _
        _ = |a p.1| * |a p.2| *
              |wilsonJacobiCorrelation w M (p.1 * p.2)| := by
          simp only [abs_mul]
        _ ≤ 1 * 1 * |wilsonJacobiCorrelation w M (p.1 * p.2)| := by
          gcongr
          · exact ha p.1
          · exact ha p.2
        _ = |wilsonJacobiCorrelation w M (p.1 * p.2)| := by ring
    by_cases hsq : IsSquare (p.1 * p.2)
    · rw [if_pos hsq]
      exact habs.trans
        ((hsquare p hp hsq).trans (le_add_of_nonneg_right hE))
    · rw [if_neg hsq, zero_add]
      exact habs.trans (hnonsquare p hp hsq)
  have hdiag :
      (((P.filter (fun p ↦ IsSquare (p.1 * p.2))).card : ℕ) : ℝ) ≤
        (N : ℝ) * (1 + Real.log (N : ℝ)) := by
    change (((squareProductPairsUpTo N).card : ℕ) : ℝ) ≤ _
    exact card_squareProductPairsUpTo_cast_le N
  have hcard : (P.card : ℝ) = (N : ℝ) ^ 2 := by
    simp [P, pow_two]
  calc
    wilsonWeightedSecondMoment a w M N =
        ∑ p ∈ P,
          a p.1 * a p.2 *
            wilsonJacobiCorrelation w M (p.1 * p.2) := by
      exact wilsonWeightedSecondMoment_eq_sum_pair_correlation a w M N
    _ ≤ ∑ p ∈ P,
        ((if IsSquare (p.1 * p.2) then D else 0) + E) :=
      Finset.sum_le_sum (fun p hp ↦ hpoint p hp)
    _ = D * ((P.filter (fun p ↦ IsSquare (p.1 * p.2))).card : ℝ) +
        E * (P.card : ℝ) := by
      simp only [Finset.sum_add_distrib]
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ D * ((N : ℝ) * (1 + Real.log (N : ℝ))) +
        E * (N : ℝ) ^ 2 := by
      rw [hcard]
      exact add_le_add (mul_le_mul_of_nonneg_left hdiag hD) le_rfl

/-- A generic direct-weight reduction: a mass bound and square/nonsquare
correlation bounds for the same weight imply a squared rectangle bound.

Wilson's neutraliser proof instead replaces the second-moment weight by a
pointwise majorant before expansion; the source-shaped version is the next
theorem. -/
theorem abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le_of_bounds
    (a b f : ℕ → ℝ) (M N : ℕ) (A Ds Ens : ℝ)
    (hf : ∀ m ∈ Finset.Icc 1 M, 0 ≤ f m)
    (hmass : wilsonWeightedMass b f M ≤ A)
    (hsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation (fun m ↦ |b m| * f m) M
            (p.1 * p.2)| ≤ Ds)
    (hnonsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ ¬ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation (fun m ↦ |b m| * f m) M
            (p.1 * p.2)| ≤ Ens) :
    |main4OrdinaryJacobiRectangle a (fun m ↦ b m * f m) M N| ^ 2 ≤
      A * (Ds + Ens) := by
  have hcauchy := abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le
    a b f M N hf
  have hmoment := wilsonWeightedSecondMoment_le_of_square_nonsquare_bounds
    a (fun m ↦ |b m| * f m) M N Ds Ens hsquare hnonsquare
  have hmass0 : 0 ≤ wilsonWeightedMass b f M := by
    unfold wilsonWeightedMass
    exact Finset.sum_nonneg (fun m hm ↦
      mul_nonneg (abs_nonneg _) (hf m hm))
  calc
    |main4OrdinaryJacobiRectangle a (fun m ↦ b m * f m) M N| ^ 2 ≤
        wilsonWeightedMass b f M *
          wilsonWeightedSecondMoment a (fun m ↦ |b m| * f m) M N := hcauchy
    _ ≤ wilsonWeightedMass b f M * (Ds + Ens) := by
      exact mul_le_mul_of_nonneg_left hmoment hmass0
    _ ≤ A * (Ds + Ens) := by
      have hsum0 : 0 ≤ Ds + Ens := by
        have hmoment0 :
            0 ≤ wilsonWeightedSecondMoment a
              (fun m ↦ |b m| * f m) M N := by
          unfold wilsonWeightedSecondMoment
          exact Finset.sum_nonneg (fun m hm ↦ by
            exact mul_nonneg
              (mul_nonneg (abs_nonneg _) (hf m hm)) (sq_nonneg _))
        linarith
      exact mul_le_mul_of_nonneg_right hmass hsum0

/-- The source-shaped finite reduction in Wilson's Section 2.  Weighted
Cauchy is followed by a pointwise neutraliser majorant of the nonnegative
second moment; only that majorant is then expanded into square and nonsquare
Jacobi correlations. -/
theorem abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le_of_majorant_bounds
    (a b f W : ℕ → ℝ) (M N : ℕ) (A Ds Ens : ℝ)
    (hf : ∀ m ∈ Finset.Icc 1 M, 0 ≤ f m)
    (hmass : wilsonWeightedMass b f M ≤ A)
    (hmajor : ∀ m ∈ Finset.Icc 1 M, |b m| * f m ≤ W m)
    (hsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation W M (p.1 * p.2)| ≤ Ds)
    (hnonsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ ¬ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation W M (p.1 * p.2)| ≤ Ens) :
    |main4OrdinaryJacobiRectangle a (fun m ↦ b m * f m) M N| ^ 2 ≤
      A * (Ds + Ens) := by
  have hcauchy := abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le
    a b f M N hf
  have hmono := wilsonWeightedSecondMoment_mono
    a (fun m ↦ |b m| * f m) W M N hmajor
  have hmomentW := wilsonWeightedSecondMoment_le_of_square_nonsquare_bounds
    a W M N Ds Ens hsquare hnonsquare
  have hmoment :
      wilsonWeightedSecondMoment a (fun m ↦ |b m| * f m) M N ≤
        Ds + Ens := hmono.trans hmomentW
  have hmass0 : 0 ≤ wilsonWeightedMass b f M := by
    unfold wilsonWeightedMass
    exact Finset.sum_nonneg (fun m hm ↦
      mul_nonneg (abs_nonneg _) (hf m hm))
  have hmoment0 :
      0 ≤ wilsonWeightedSecondMoment a
        (fun m ↦ |b m| * f m) M N := by
    unfold wilsonWeightedSecondMoment
    exact Finset.sum_nonneg (fun m hm ↦
      mul_nonneg (mul_nonneg (abs_nonneg _) (hf m hm)) (sq_nonneg _))
  have hsum0 : 0 ≤ Ds + Ens := hmoment0.trans hmoment
  calc
    |main4OrdinaryJacobiRectangle a (fun m ↦ b m * f m) M N| ^ 2 ≤
        wilsonWeightedMass b f M *
          wilsonWeightedSecondMoment a (fun m ↦ |b m| * f m) M N := hcauchy
    _ ≤ wilsonWeightedMass b f M * (Ds + Ens) :=
      mul_le_mul_of_nonneg_left hmoment hmass0
    _ ≤ A * (Ds + Ens) :=
      mul_le_mul_of_nonneg_right hmass hsum0

end

end PellPaper
