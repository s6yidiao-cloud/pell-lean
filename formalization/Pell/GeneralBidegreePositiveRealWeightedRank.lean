import Pell.GeneralBidegreeRealWeightedSupportContainment
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The untruncated positive real weighted rank cap

For strictly positive `ellM`, the real weight condition

`i * ellM + j * ellX ≤ R`

already cuts out a finite set of bivariate monomial exponents.  This file
removes the auxiliary total-degree cutoff from the real weighted-support
bridge and proves the resulting finite rank cap.  It is the exact
finite-dimensional form of the `N(R) - N(R-(A+1)ell_x)` mechanism in
`L:sheared`; it intentionally contains no lattice-point asymptotic.
-/

namespace PellPaper

open scoped BigOperators Pointwise

/-- Under `ellM ≤ ellX`, ordinary degree times `ellM` is bounded by the
two-coordinate real weight. -/
theorem generalBidegreeDegree_mul_ellM_le_realWeight
    (ellM ellX : ℝ) (hell : ellM ≤ ellX)
    (m : generalBidegreeWeightedMonomialIndex) :
    ((Finsupp.degree m : ℕ) : ℝ) * ellM ≤
      generalBidegreeRealWeight ellM ellX m := by
  have hdegree : Finsupp.degree m = m 0 + m 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hmone_nonneg : 0 ≤ (m 1 : ℝ) := by positivity
  have hmul : (m 1 : ℝ) * ellM ≤ (m 1 : ℝ) * ellX :=
    mul_le_mul_of_nonneg_left hell hmone_nonneg
  rw [hdegree]
  push_cast
  calc
    ((m 0 : ℝ) + (m 1 : ℝ)) * ellM =
        (m 0 : ℝ) * ellM + (m 1 : ℝ) * ellM := by ring
    _ ≤ (m 0 : ℝ) * ellM + (m 1 : ℝ) * ellX :=
      add_le_add (le_refl _) hmul

/-- Strict positivity of the smaller weight makes the untruncated real
weight ball finite. -/
theorem finite_generalBidegreeRealWeightSet
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    {m : generalBidegreeWeightedMonomialIndex |
      generalBidegreeRealWeight ellM ellX m ≤ R}.Finite := by
  let D : ℕ := ⌈R / ellM⌉₊
  apply (Finsupp.finite_of_degree_le D).subset
  intro m hm
  have hmul : ((Finsupp.degree m : ℕ) : ℝ) * ellM ≤ R :=
    (generalBidegreeDegree_mul_ellM_le_realWeight ellM ellX hell m).trans hm
  have hdiv : ((Finsupp.degree m : ℕ) : ℝ) ≤ R / ellM :=
    (le_div_iff₀ hellM_pos).mpr hmul
  have hceil : R / ellM ≤ (D : ℝ) := by
    dsimp only [D]
    exact Nat.le_ceil _
  exact_mod_cast hdiv.trans hceil

/-- The finite set of all exponent vectors satisfying the positive real
weight condition, with no externally supplied degree cutoff. -/
noncomputable def generalBidegreePositiveRealWeightedBall
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    Finset generalBidegreeWeightedMonomialIndex :=
  Set.Finite.toFinset
    (finite_generalBidegreeRealWeightSet ellM ellX R hellM_pos hell)

@[simp]
theorem mem_generalBidegreePositiveRealWeightedBall_iff
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (m : generalBidegreeWeightedMonomialIndex) :
    m ∈ generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell ↔
      generalBidegreeRealWeight ellM ellX m ≤ R := by
  classical
  simp [generalBidegreePositiveRealWeightedBall]

/-- The exact untruncated support transport: multiplying by `P_A` increases
the real weight budget by at most `(A+1) * ellX`. -/
theorem support_generalBidegreeParallelLinePolynomial_mul_monomial_subset_positiveReal
    (A : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) :
    (generalBidegreeParallelLinePolynomial A *
      MvPolynomial.monomial m (1 : ℚ)).support ⊆
        generalBidegreePositiveRealWeightedBall ellM ellX
          (R + ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell := by
  intro k hk
  rw [mem_generalBidegreePositiveRealWeightedBall_iff]
  have hmul : k ∈ (generalBidegreeParallelLinePolynomial A).support +
      (MvPolynomial.monomial m (1 : ℚ)).support :=
    MvPolynomial.support_mul _ _ hk
  rcases Finset.mem_add.mp hmul with ⟨n, hn, q, hq, hnq⟩
  have hq_singleton : q ∈ ({m} : Finset generalBidegreeWeightedMonomialIndex) :=
    MvPolynomial.support_monomial_subset hq
  have hqeq : q = m := Finset.mem_singleton.mp hq_singleton
  subst q
  have hm_weight : generalBidegreeRealWeight ellM ellX m ≤ R :=
    (mem_generalBidegreePositiveRealWeightedBall_iff
      ellM ellX R hellM_pos hell m).mp hm
  have hn_weight : generalBidegreeRealWeight ellM ellX n ≤
      ((A + 1 : ℕ) : ℝ) * ellX :=
    generalBidegreeRealWeight_le_parallelLinePolynomial_weightBound
      A ellM ellX hellM_pos.le hell hn
  rw [← hnq, generalBidegreeRealWeight_add]
  linarith

/-- The untruncated real support transport as monomial-span membership. -/
theorem generalBidegreeParallelLinePolynomial_mul_monomial_mem_positiveRealWeightedSpan
    (A : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) :
    generalBidegreeParallelLinePolynomial A *
      MvPolynomial.monomial m (1 : ℚ) ∈
        generalBidegreeCoefficientMonomialSpan
          (generalBidegreePositiveRealWeightedBall ellM ellX
            (R + ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell) := by
  apply mem_generalBidegreeCoefficientMonomialSpan_of_support_subset
  exact support_generalBidegreeParallelLinePolynomial_mul_monomial_subset_positiveReal
    A ellM ellX R hellM_pos hell hm

/-- The untruncated positive-real weighted rank cap.  This is the exact
finite-rank inequality behind the source's `N(R)` subtraction. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX
        (R + ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell) ≤
      (generalBidegreePositiveRealWeightedBall ellM ellX
        (R + ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card := by
  apply generalBidegreeCoefficientEvaluationRank_le_card_sub_card
  intro m
  exact generalBidegreeParallelLinePolynomial_mul_monomial_mem_positiveRealWeightedSpan
    A ellM ellX R hellM_pos hell m.property

/-- The same rank cap in the source's `N(R) - N(R-(A+1)ellX)` form.  The
ball is well-defined even when the shifted radius is negative (then it is
simply empty). -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card := by
  simpa only [sub_add_cancel] using
    generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le
      A B ellM ellX (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell

end PellPaper
