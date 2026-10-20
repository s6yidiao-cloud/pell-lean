import Pell.WilsonReciprocalDivisorNeutralizer
import Pell.WilsonWeightedCauchyReduction

/-!
# Wilson's neutralizer inserted into weighted Cauchy

This module joins the two finite parts of Wilson's Section 2 argument.  The
specialized Lemma 2.1 neutralizer majorizes `|b m| / tau(m)` pointwise, and
the source-shaped weighted-Cauchy reduction then leaves only the square and
nonsquare correlations of that neutralizer.

No support estimate, fundamental sieve lemma, or character-sum estimate is
asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The Hooley-neutralizer majorant attached to a finite squarefree sieve
product `P` and upper-Moebius coefficients `lambdaPlus`. -/
def main4WilsonNeutralizerMajorant
    (P : ℕ) (lambdaPlus : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d ↦ d ∣ P),
    lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d

/-- The source-shaped majorant retains the odd support of `b`.  This matters
after the divisor change of variables: Wilson applies Pólya--Vinogradov to
the odd-denominator character `(q / k)`. -/
def main4WilsonOddNeutralizerMajorant
    (P : ℕ) (lambdaPlus : ℕ → ℝ) (m : ℕ) : ℝ :=
  if Odd m then main4WilsonNeutralizerMajorant P lambdaPlus m else 0

/-- Wilson's specialized Lemma 2.1, named as a pointwise majorant. -/
theorem main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
    (P m : ℕ) (hP : Squarefree P) (hm : m ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    main4WilsonReciprocalDivisorWeight m ≤
      main4WilsonNeutralizerMajorant P lambdaPlus m := by
  exact main4WilsonReciprocalDivisorWeight_le_neutralizer
    P m hP hm lambdaPlus hUpper

/-- A coefficient bounded by one may be inserted before applying the
neutralizer.  Positivity comes from the reciprocal-divisor weight, not from
the neutralizer coefficients term by term. -/
theorem abs_mul_main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
    (P m : ℕ) (hP : Squarefree P) (hm : m ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    {b : ℕ → ℝ} (hb : |b m| ≤ 1) :
    |b m| * main4WilsonReciprocalDivisorWeight m ≤
      main4WilsonNeutralizerMajorant P lambdaPlus m := by
  calc
    |b m| * main4WilsonReciprocalDivisorWeight m ≤
        1 * main4WilsonReciprocalDivisorWeight m := by
      exact mul_le_mul_of_nonneg_right hb
        (main4WilsonReciprocalDivisorWeight_nonneg m)
    _ = main4WilsonReciprocalDivisorWeight m := one_mul _
    _ ≤ main4WilsonNeutralizerMajorant P lambdaPlus m :=
      main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
        P m hP hm lambdaPlus hUpper

/-- Odd-supported version of the pointwise majorization, matching Wilson's
coefficient hypothesis without adding spurious even denominators. -/
theorem abs_mul_main4WilsonReciprocalDivisorWeight_le_oddNeutralizerMajorant
    (P m : ℕ) (hP : Squarefree P) (hm : m ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    {b : ℕ → ℝ} (hb : main4OddSupportedUnitBound b) :
    |b m| * main4WilsonReciprocalDivisorWeight m ≤
      main4WilsonOddNeutralizerMajorant P lambdaPlus m := by
  unfold main4WilsonOddNeutralizerMajorant
  by_cases hodd : Odd m
  · rw [if_pos hodd]
    exact
      abs_mul_main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
        P m hP hm lambdaPlus hUpper (hb.2 m)
  · rw [if_neg hodd, hb.1 m (Nat.not_odd_iff_even.mp hodd)]
    simp

/-- Exact finite handoff after inserting Wilson's Lemma 2.1 into weighted
Cauchy.  Bounds for the square and nonsquare neutralizer correlations imply
the squared rectangle estimate. -/
theorem abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_of_neutralizer_bounds
    (a b : ℕ → ℝ) (P M N : ℕ) (lambdaPlus : ℕ → ℝ)
    (A Ds Ens : ℝ)
    (hP : Squarefree P)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (hb : ∀ m : ℕ, |b m| ≤ 1)
    (hmass :
      wilsonWeightedMass b main4WilsonReciprocalDivisorWeight M ≤ A)
    (hsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤ Ds)
    (hnonsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ ¬ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤ Ens) :
    |main4OrdinaryJacobiRectangle a
        (fun m ↦ b m * main4WilsonReciprocalDivisorWeight m) M N| ^ 2 ≤
      A * (Ds + Ens) := by
  apply abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le_of_majorant_bounds
    a b main4WilsonReciprocalDivisorWeight
      (main4WilsonNeutralizerMajorant P lambdaPlus)
      M N A Ds Ens
  · intro m _hm
    exact main4WilsonReciprocalDivisorWeight_nonneg m
  · exact hmass
  · intro m hm
    exact
      abs_mul_main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
        P m hP (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1) lambdaPlus hUpper
          (hb m)
  · exact hsquare
  · exact hnonsquare

/-- Fully source-shaped finite handoff, retaining the odd support while the
neutralizer majorizes the second moment. -/
theorem abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_of_oddNeutralizer_bounds
    (a b : ℕ → ℝ) (P M N : ℕ) (lambdaPlus : ℕ → ℝ)
    (A Ds Ens : ℝ)
    (hP : Squarefree P)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (hb : main4OddSupportedUnitBound b)
    (hmass :
      wilsonWeightedMass b main4WilsonReciprocalDivisorWeight M ≤ A)
    (hsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤ Ds)
    (hnonsquare :
      |∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
          (fun p ↦ ¬ IsSquare (p.1 * p.2)),
        a p.1 * a p.2 *
          wilsonJacobiCorrelation
            (main4WilsonOddNeutralizerMajorant P lambdaPlus) M
            (p.1 * p.2)| ≤ Ens) :
    |main4OrdinaryJacobiRectangle a
        (fun m ↦ b m * main4WilsonReciprocalDivisorWeight m) M N| ^ 2 ≤
      A * (Ds + Ens) := by
  apply abs_main4OrdinaryJacobiRectangle_mul_weight_sq_le_of_majorant_bounds
    a b main4WilsonReciprocalDivisorWeight
      (main4WilsonOddNeutralizerMajorant P lambdaPlus)
      M N A Ds Ens
  · intro m _hm
    exact main4WilsonReciprocalDivisorWeight_nonneg m
  · exact hmass
  · intro m hm
    exact
      abs_mul_main4WilsonReciprocalDivisorWeight_le_oddNeutralizerMajorant
        P m hP (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1) lambdaPlus hUpper hb
  · exact hsquare
  · exact hnonsquare

end

end PellPaper
