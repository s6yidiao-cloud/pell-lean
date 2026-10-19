import Pell.GeneralBidegreeWeightedSupportContainment
import Mathlib.Data.Real.Basic

/-!
# Real weighted support containment for the parallel-line polynomial

This is the real-weight counterpart of
`GeneralBidegreeWeightedSupportContainment`.  It uses the logarithmic-style
weight

`i * ellM + j * ellX`

on coefficient monomials.  An explicit total-degree cutoff keeps every
support finite, including the endpoint `ellM = 0`.  Thus no discretization of
the source weights is needed for the finite rank-filtration statement.
-/

namespace PellPaper

open scoped BigOperators Pointwise

/-- The real two-coordinate weight used by the sheared Taylor expansion. -/
def generalBidegreeRealWeight (ellM ellX : ℝ)
    (m : generalBidegreeWeightedMonomialIndex) : ℝ :=
  (m 0 : ℝ) * ellM + (m 1 : ℝ) * ellX

/-- A finite real-weight support: total degree at most `D` and weight at
most `R`. -/
noncomputable def generalBidegreeRealWeightedBall (D : ℕ)
    (ellM ellX R : ℝ) : Finset generalBidegreeWeightedMonomialIndex :=
  (generalBidegreeDegreeBall D).filter
    (fun m => generalBidegreeRealWeight ellM ellX m ≤ R)

@[simp]
theorem mem_generalBidegreeRealWeightedBall_iff
    (D : ℕ) (ellM ellX R : ℝ)
    (m : generalBidegreeWeightedMonomialIndex) :
    m ∈ generalBidegreeRealWeightedBall D ellM ellX R ↔
      Finsupp.degree m ≤ D ∧ generalBidegreeRealWeight ellM ellX m ≤ R := by
  classical
  simp [generalBidegreeRealWeightedBall]

theorem generalBidegreeRealWeight_add (ellM ellX : ℝ)
    (m n : generalBidegreeWeightedMonomialIndex) :
    generalBidegreeRealWeight ellM ellX (m + n) =
      generalBidegreeRealWeight ellM ellX m +
        generalBidegreeRealWeight ellM ellX n := by
  simp only [generalBidegreeRealWeight, Finsupp.add_apply, Nat.cast_add]
  ring

/-- If `0 ≤ ellM ≤ ellX`, a real two-coordinate weight is bounded by total
degree times `ellX`. -/
theorem generalBidegreeRealWeight_le_degree_mul
    (ellM ellX : ℝ) (hell : ellM ≤ ellX)
    (m : generalBidegreeWeightedMonomialIndex) :
    generalBidegreeRealWeight ellM ellX m ≤ ((Finsupp.degree m : ℕ) : ℝ) * ellX := by
  have hdegree : Finsupp.degree m = m 0 + m 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hmzero : 0 ≤ (m 0 : ℝ) := by positivity
  have hmul : (m 0 : ℝ) * ellM ≤ (m 0 : ℝ) * ellX :=
    mul_le_mul_of_nonneg_left hell hmzero
  rw [hdegree]
  push_cast
  calc
    (m 0 : ℝ) * ellM + (m 1 : ℝ) * ellX ≤
        (m 0 : ℝ) * ellX + (m 1 : ℝ) * ellX :=
      add_le_add hmul (le_refl _)
    _ = ((m 0 : ℝ) + (m 1 : ℝ)) * ellX := by ring

/-- Every exponent in the support of the parallel-line polynomial has real
weight at most `(A+1) * ellX`. -/
theorem generalBidegreeRealWeight_le_parallelLinePolynomial_weightBound
    (A : ℕ) (ellM ellX : ℝ) (hellM_nonneg : 0 ≤ ellM) (hell : ellM ≤ ellX)
    {n : generalBidegreeWeightedMonomialIndex}
    (hn : n ∈ (generalBidegreeParallelLinePolynomial A).support) :
    generalBidegreeRealWeight ellM ellX n ≤ ((A + 1 : ℕ) : ℝ) * ellX := by
  have hellX_nonneg : 0 ≤ ellX := hellM_nonneg.trans hell
  have hdegree : Finsupp.degree n ≤
      (generalBidegreeParallelLinePolynomial A).totalDegree := by
    change n.sum (fun _ e => e) ≤
      (generalBidegreeParallelLinePolynomial A).totalDegree
    exact MvPolynomial.le_totalDegree hn
  calc
    generalBidegreeRealWeight ellM ellX n ≤ ((Finsupp.degree n : ℕ) : ℝ) * ellX :=
      generalBidegreeRealWeight_le_degree_mul ellM ellX hell n
    _ ≤ ((generalBidegreeParallelLinePolynomial A).totalDegree : ℝ) * ellX := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) hellX_nonneg
    _ ≤ ((A + 1 : ℕ) : ℝ) * ellX := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast totalDegree_generalBidegreeParallelLinePolynomial_le A)
        hellX_nonneg

/-- Multiplication by `P_A` transports a real weighted monomial support into
the ball whose degree radius rises by `A+1` and whose weight radius rises by
`(A+1) * ellX`. -/
theorem support_generalBidegreeParallelLinePolynomial_mul_monomial_subset_real
    (A D : ℕ) (ellM ellX R : ℝ)
    (hellM_nonneg : 0 ≤ ellM) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreeRealWeightedBall D ellM ellX R) :
    (generalBidegreeParallelLinePolynomial A *
      MvPolynomial.monomial m (1 : ℚ)).support ⊆
        generalBidegreeRealWeightedBall (D + (A + 1)) ellM ellX
          (R + ((A + 1 : ℕ) : ℝ) * ellX) := by
  intro k hk
  rw [mem_generalBidegreeRealWeightedBall_iff]
  have hmul : k ∈ (generalBidegreeParallelLinePolynomial A).support +
      (MvPolynomial.monomial m (1 : ℚ)).support :=
    MvPolynomial.support_mul _ _ hk
  rcases Finset.mem_add.mp hmul with ⟨n, hn, q, hq, hnq⟩
  have hq_singleton : q ∈ ({m} : Finset generalBidegreeWeightedMonomialIndex) :=
    MvPolynomial.support_monomial_subset hq
  have hqeq : q = m := Finset.mem_singleton.mp hq_singleton
  subst q
  have hm_degree : Finsupp.degree m ≤ D :=
    (mem_generalBidegreeRealWeightedBall_iff D ellM ellX R m).mp hm |>.1
  have hm_weight : generalBidegreeRealWeight ellM ellX m ≤ R :=
    (mem_generalBidegreeRealWeightedBall_iff D ellM ellX R m).mp hm |>.2
  have hn_degree : Finsupp.degree n ≤ A + 1 := by
    have hdegree : Finsupp.degree n ≤
        (generalBidegreeParallelLinePolynomial A).totalDegree := by
      change n.sum (fun _ e => e) ≤
        (generalBidegreeParallelLinePolynomial A).totalDegree
      exact MvPolynomial.le_totalDegree hn
    exact hdegree.trans (totalDegree_generalBidegreeParallelLinePolynomial_le A)
  have hn_weight : generalBidegreeRealWeight ellM ellX n ≤
      ((A + 1 : ℕ) : ℝ) * ellX :=
    generalBidegreeRealWeight_le_parallelLinePolynomial_weightBound
      A ellM ellX hellM_nonneg hell hn
  constructor
  · rw [← hnq, map_add]
    omega
  · rw [← hnq, generalBidegreeRealWeight_add]
    linarith

/-- The real-weight support containment as span membership, directly usable
by the finite-support rank-cap theorem. -/
theorem generalBidegreeParallelLinePolynomial_mul_monomial_mem_realWeightedSpan
    (A D : ℕ) (ellM ellX R : ℝ)
    (hellM_nonneg : 0 ≤ ellM) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreeRealWeightedBall D ellM ellX R) :
    generalBidegreeParallelLinePolynomial A *
      MvPolynomial.monomial m (1 : ℚ) ∈
        generalBidegreeCoefficientMonomialSpan
          (generalBidegreeRealWeightedBall (D + (A + 1)) ellM ellX
            (R + ((A + 1 : ℕ) : ℝ) * ellX)) := by
  apply mem_generalBidegreeCoefficientMonomialSpan_of_support_subset
  exact support_generalBidegreeParallelLinePolynomial_mul_monomial_subset_real
    A D ellM ellX R hellM_nonneg hell hm

/-- A direct real-weight rank cap.  It packages the ideal-kernel subtraction
with the exact real support transport; no lattice-point asymptotic is used. -/
theorem generalBidegreeCoefficientEvaluationRank_realWeightedBall_le
    (A B D : ℕ) (ellM ellX R : ℝ)
    (hellM_nonneg : 0 ≤ ellM) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreeRealWeightedBall (D + (A + 1)) ellM ellX
        (R + ((A + 1 : ℕ) : ℝ) * ellX)) ≤
      (generalBidegreeRealWeightedBall (D + (A + 1)) ellM ellX
        (R + ((A + 1 : ℕ) : ℝ) * ellX)).card -
        (generalBidegreeRealWeightedBall D ellM ellX R).card := by
  apply generalBidegreeCoefficientEvaluationRank_le_card_sub_card
  intro m
  exact generalBidegreeParallelLinePolynomial_mul_monomial_mem_realWeightedSpan
    A D ellM ellX R hellM_nonneg hell m.property

end PellPaper
