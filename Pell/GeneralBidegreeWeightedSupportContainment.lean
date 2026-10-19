import Pell.GeneralBidegreeParallelRankBound
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted finite-support containment for the parallel-line polynomial

This module supplies the finite-support input missing from the rank cap in
`GeneralBidegreeParallelRankBound`.  A support is cut off both by ordinary
total degree and by a two-coordinate nonnegative weight.  The degree cutoff
makes the support finite even when one of the two weights is zero.

The main theorem proves that multiplying a monomial in the shifted ball by
the parallel-line polynomial `P_A` stays in the larger ball whose weight
radius has increased by `(A + 1) * ellX`.
-/

namespace PellPaper

open scoped BigOperators Pointwise

abbrev generalBidegreeWeightedMonomialIndex := Fin 2 →₀ ℕ

/-- The two-coordinate natural weight corresponding to
`i * ellM + j * ellX`. -/
def generalBidegreeNatWeight (ellM ellX : ℕ)
    (m : generalBidegreeWeightedMonomialIndex) : ℕ :=
  m 0 * ellM + m 1 * ellX

/-- All bivariate exponent vectors of total degree at most `D`. -/
noncomputable def generalBidegreeDegreeBall (D : ℕ) :
    Finset generalBidegreeWeightedMonomialIndex :=
  Set.Finite.toFinset (Finsupp.finite_of_degree_le (σ := Fin 2) D)

/-- A finite weighted support: total degree at most `D` and two-coordinate
weight at most `R`. -/
noncomputable def generalBidegreeWeightedBall (D ellM ellX R : ℕ) :
    Finset generalBidegreeWeightedMonomialIndex :=
  (generalBidegreeDegreeBall D).filter
    (fun m => generalBidegreeNatWeight ellM ellX m ≤ R)

@[simp]
theorem mem_generalBidegreeDegreeBall_iff
    (D : ℕ) (m : generalBidegreeWeightedMonomialIndex) :
    m ∈ generalBidegreeDegreeBall D ↔ Finsupp.degree m ≤ D := by
  classical
  simp [generalBidegreeDegreeBall]

@[simp]
theorem mem_generalBidegreeWeightedBall_iff
    (D ellM ellX R : ℕ) (m : generalBidegreeWeightedMonomialIndex) :
    m ∈ generalBidegreeWeightedBall D ellM ellX R ↔
      Finsupp.degree m ≤ D ∧ generalBidegreeNatWeight ellM ellX m ≤ R := by
  classical
  simp [generalBidegreeWeightedBall]

theorem generalBidegreeNatWeight_add (ellM ellX : ℕ)
    (m n : generalBidegreeWeightedMonomialIndex) :
    generalBidegreeNatWeight ellM ellX (m + n) =
      generalBidegreeNatWeight ellM ellX m +
        generalBidegreeNatWeight ellM ellX n := by
  simp only [generalBidegreeNatWeight, Finsupp.add_apply, Nat.add_mul]
  ac_rfl

/-- Under `ellM ≤ ellX`, the two-coordinate weight of a monomial is bounded
by its ordinary degree times `ellX`. -/
theorem generalBidegreeNatWeight_le_degree_mul (ellM ellX : ℕ)
    (hell : ellM ≤ ellX) (m : generalBidegreeWeightedMonomialIndex) :
    generalBidegreeNatWeight ellM ellX m ≤ Finsupp.degree m * ellX := by
  have hdegree : Finsupp.degree m = m 0 + m 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [hdegree, generalBidegreeNatWeight]
  calc
    m 0 * ellM + m 1 * ellX ≤ m 0 * ellX + m 1 * ellX :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hell) _
    _ = (m 0 + m 1) * ellX := (Nat.add_mul _ _ _).symm

/-- Each linear factor in the parallel-line polynomial has total degree at
most one. -/
theorem totalDegree_parallelLineFactor_le_one (a : ℕ) :
    (MvPolynomial.X (0 : Fin 2) - 2 * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (a : ℚ)).totalDegree ≤ 1 := by
  have htwo : (2 * MvPolynomial.X (1 : Fin 2) :
      MvPolynomial (Fin 2) ℚ).totalDegree ≤ 1 := by
    calc
      (2 * MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ).totalDegree ≤
          (2 : MvPolynomial (Fin 2) ℚ).totalDegree +
            (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = 1 := by
        change (MvPolynomial.C (2 : ℚ) : MvPolynomial (Fin 2) ℚ).totalDegree +
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ).totalDegree = 1
        simp
  calc
    (MvPolynomial.X (0 : Fin 2) - 2 * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (a : ℚ)).totalDegree ≤
        max ((MvPolynomial.X (0 : Fin 2) - 2 * MvPolynomial.X (1 : Fin 2) :
          MvPolynomial (Fin 2) ℚ).totalDegree)
          ((MvPolynomial.C (a : ℚ) : MvPolynomial (Fin 2) ℚ).totalDegree) :=
      MvPolynomial.totalDegree_sub _ _
    _ ≤ max 1 0 := by
      apply max_le
      · exact (MvPolynomial.totalDegree_sub _ _).trans
          (max_le (by simp) htwo)
      · simp only [MvPolynomial.totalDegree_C]
        omega
    _ = 1 := by simp

/-- The parallel-line polynomial has ordinary total degree at most `A+1`. -/
theorem totalDegree_generalBidegreeParallelLinePolynomial_le (A : ℕ) :
    (generalBidegreeParallelLinePolynomial A).totalDegree ≤ A + 1 := by
  rw [generalBidegreeParallelLinePolynomial]
  calc
    (∏ a ∈ Finset.range (A + 1),
      (MvPolynomial.X (0 : Fin 2) - 2 * MvPolynomial.X (1 : Fin 2) -
        MvPolynomial.C (a : ℚ))).totalDegree ≤
        ∑ a ∈ Finset.range (A + 1),
          (MvPolynomial.X (0 : Fin 2) - 2 * MvPolynomial.X (1 : Fin 2) -
            MvPolynomial.C (a : ℚ)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _a ∈ Finset.range (A + 1), 1 := by
      exact Finset.sum_le_sum fun a ha => totalDegree_parallelLineFactor_le_one a
    _ = A + 1 := by simp

/-- Every exponent in the support of the parallel-line polynomial has weight
at most `(A+1) * ellX` when `ellM ≤ ellX`. -/
theorem generalBidegreeNatWeight_le_parallelLinePolynomial_weightBound
    (A ellM ellX : ℕ) (hell : ellM ≤ ellX)
    {n : generalBidegreeWeightedMonomialIndex}
    (hn : n ∈ (generalBidegreeParallelLinePolynomial A).support) :
    generalBidegreeNatWeight ellM ellX n ≤ (A + 1) * ellX := by
  have hdegree : Finsupp.degree n ≤
      (generalBidegreeParallelLinePolynomial A).totalDegree := by
    change n.sum (fun _ e => e) ≤
      (generalBidegreeParallelLinePolynomial A).totalDegree
    exact MvPolynomial.le_totalDegree hn
  calc
    generalBidegreeNatWeight ellM ellX n ≤ Finsupp.degree n * ellX :=
      generalBidegreeNatWeight_le_degree_mul ellM ellX hell n
    _ ≤ (generalBidegreeParallelLinePolynomial A).totalDegree * ellX :=
      Nat.mul_le_mul_right ellX hdegree
    _ ≤ (A + 1) * ellX :=
      Nat.mul_le_mul_right ellX
        (totalDegree_generalBidegreeParallelLinePolynomial_le A)

/-- Multiplication by the parallel-line polynomial transports a bounded
weighted monomial support into the ball with degree radius increased by
`A+1` and weight radius increased by `(A+1) * ellX`. -/
theorem support_generalBidegreeParallelLinePolynomial_mul_monomial_subset
    (A D ellM ellX R : ℕ) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreeWeightedBall D ellM ellX R) :
    (generalBidegreeParallelLinePolynomial A *
      MvPolynomial.monomial m (1 : ℚ)).support ⊆
        generalBidegreeWeightedBall (D + (A + 1)) ellM ellX
          (R + (A + 1) * ellX) := by
  intro k hk
  rw [mem_generalBidegreeWeightedBall_iff]
  have hmul : k ∈ (generalBidegreeParallelLinePolynomial A).support +
      (MvPolynomial.monomial m (1 : ℚ)).support :=
    MvPolynomial.support_mul _ _ hk
  rcases Finset.mem_add.mp hmul with ⟨n, hn, q, hq, hnq⟩
  have hq_singleton : q ∈ ({m} : Finset generalBidegreeWeightedMonomialIndex) :=
    MvPolynomial.support_monomial_subset hq
  have hqeq : q = m := Finset.mem_singleton.mp hq_singleton
  subst q
  have hm_degree : Finsupp.degree m ≤ D :=
    (mem_generalBidegreeWeightedBall_iff D ellM ellX R m).mp hm |>.1
  have hm_weight : generalBidegreeNatWeight ellM ellX m ≤ R :=
    (mem_generalBidegreeWeightedBall_iff D ellM ellX R m).mp hm |>.2
  have hn_degree : Finsupp.degree n ≤ A + 1 := by
    have hdegree : Finsupp.degree n ≤
        (generalBidegreeParallelLinePolynomial A).totalDegree := by
      change n.sum (fun _ e => e) ≤
        (generalBidegreeParallelLinePolynomial A).totalDegree
      exact MvPolynomial.le_totalDegree hn
    exact hdegree.trans (totalDegree_generalBidegreeParallelLinePolynomial_le A)
  have hn_weight : generalBidegreeNatWeight ellM ellX n ≤ (A + 1) * ellX :=
    generalBidegreeNatWeight_le_parallelLinePolynomial_weightBound A ellM ellX hell hn
  constructor
  · rw [← hnq, map_add]
    omega
  · rw [← hnq, generalBidegreeNatWeight_add]
    omega

/-- A polynomial whose monomial support is contained in a finite exponent
support belongs to the corresponding monomial span. -/
theorem mem_generalBidegreeCoefficientMonomialSpan_of_support_subset
    (U : Finset generalBidegreeCoefficientMonomialIndex)
    {p : MvPolynomial (Fin 2) ℚ}
    (hp : p.support ⊆ U) :
    p ∈ generalBidegreeCoefficientMonomialSpan U := by
  classical
  rw [generalBidegreeCoefficientMonomialSpan, MvPolynomial.as_sum p]
  apply Submodule.sum_mem
  intro n hn
  have hgenerator : MvPolynomial.monomial n (1 : ℚ) ∈
      Submodule.span ℚ (generalBidegreeCoefficientMonomialFinset U : Set _) := by
    apply Submodule.subset_span
    change MvPolynomial.monomial n (1 : ℚ) ∈
      generalBidegreeCoefficientMonomialFinset U
    unfold generalBidegreeCoefficientMonomialFinset
    exact Finset.mem_image.mpr ⟨n, hp hn, rfl⟩
  rw [show MvPolynomial.monomial n (MvPolynomial.coeff n p) =
      MvPolynomial.coeff n p • MvPolynomial.monomial n (1 : ℚ) by
        simpa using (MvPolynomial.smul_monomial
          (a := (1 : ℚ)) (s := n) (MvPolynomial.coeff n p)).symm]
  exact Submodule.smul_mem _ _ hgenerator

/-- The support containment above, recast as the precise span membership
needed by the finite-support rank cap. -/
theorem generalBidegreeParallelLinePolynomial_mul_monomial_mem_weightedSpan
    (A D ellM ellX R : ℕ) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreeWeightedBall D ellM ellX R) :
    generalBidegreeParallelLinePolynomial A *
      MvPolynomial.monomial m (1 : ℚ) ∈
        generalBidegreeCoefficientMonomialSpan
          (generalBidegreeWeightedBall (D + (A + 1)) ellM ellX
            (R + (A + 1) * ellX)) := by
  apply mem_generalBidegreeCoefficientMonomialSpan_of_support_subset
  exact support_generalBidegreeParallelLinePolynomial_mul_monomial_subset
    A D ellM ellX R hell hm

/-- The parallel-line ideal gives an explicit rank cap for the two bounded
weighted supports.  This is the finite version of the kernel subtraction in
`e:shear-rankcap`; the later lattice-point calculation is responsible only
for estimating the two displayed finite cardinalities. -/
theorem generalBidegreeCoefficientEvaluationRank_weightedBall_le
    (A B D ellM ellX R : ℕ) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreeWeightedBall (D + (A + 1)) ellM ellX
        (R + (A + 1) * ellX)) ≤
      (generalBidegreeWeightedBall (D + (A + 1)) ellM ellX
        (R + (A + 1) * ellX)).card -
        (generalBidegreeWeightedBall D ellM ellX R).card := by
  apply generalBidegreeCoefficientEvaluationRank_le_card_sub_card
  intro m
  exact generalBidegreeParallelLinePolynomial_mul_monomial_mem_weightedSpan
    A D ellM ellX R hell m.property

end PellPaper
