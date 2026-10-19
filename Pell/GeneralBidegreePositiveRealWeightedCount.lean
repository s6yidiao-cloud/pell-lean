import Pell.GeneralBidegreePositiveRealWeightedRank
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Elementary lattice bounds for the positive real weighted ball

This file gives a fully finite, source-compatible lattice-count estimate for
the bivariate weighted ball used in the parallel-line rank cap.  Positivity
of the two weights bounds each exponent coordinate separately, so the ball
injects into an explicit rectangle of natural-number intervals.

The result is deliberately elementary: it is a rigorous finite replacement
for the first, coarse part of the lattice-point calculation, rather than the
piecewise asymptotic used later in the manuscript.
-/

namespace PellPaper

/-- The first exponent coordinate of a monomial in the positive real
weighted ball is bounded by the corresponding natural floor. -/
theorem generalBidegreeCoordinateZero_le_floor_div_of_mem_positiveRealWeightedBall
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) :
    m 0 ≤ ⌊R / ellM⌋₊ := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hm_weight : generalBidegreeRealWeight ellM ellX m ≤ R :=
    (mem_generalBidegreePositiveRealWeightedBall_iff
      ellM ellX R hellM_pos hell m).mp hm
  have hsecond_nonneg : 0 ≤ (m 1 : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hfirst : (m 0 : ℝ) * ellM ≤ R := by
    rw [generalBidegreeRealWeight] at hm_weight
    linarith
  have hdiv : (m 0 : ℝ) ≤ R / ellM :=
    (le_div_iff₀ hellM_pos).mpr hfirst
  exact Nat.le_floor hdiv

/-- The second exponent coordinate of a monomial in the positive real
weighted ball is bounded by the corresponding natural floor. -/
theorem generalBidegreeCoordinateOne_le_floor_div_of_mem_positiveRealWeightedBall
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    {m : generalBidegreeWeightedMonomialIndex}
    (hm : m ∈ generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) :
    m 1 ≤ ⌊R / ellX⌋₊ := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hm_weight : generalBidegreeRealWeight ellM ellX m ≤ R :=
    (mem_generalBidegreePositiveRealWeightedBall_iff
      ellM ellX R hellM_pos hell m).mp hm
  have hfirst_nonneg : 0 ≤ (m 0 : ℝ) * ellM :=
    mul_nonneg (by positivity) hellM_pos.le
  have hsecond : (m 1 : ℝ) * ellX ≤ R := by
    rw [generalBidegreeRealWeight] at hm_weight
    linarith
  have hdiv : (m 1 : ℝ) ≤ R / ellX :=
    (le_div_iff₀ hellX_pos).mpr hsecond
  exact Nat.le_floor hdiv

/-- A concrete rectangular lattice-count bound for the untruncated positive
real weighted ball.  It applies at every real radius; for a negative radius
the ball is empty, and the same inequality remains valid. -/
theorem card_generalBidegreePositiveRealWeightedBall_le_rectangle
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card ≤
      (⌊R / ellM⌋₊ + 1) * (⌊R / ellX⌋₊ + 1) := by
  let f : ↥(generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) →
      Fin (⌊R / ellM⌋₊ + 1) × Fin (⌊R / ellX⌋₊ + 1) := fun m =>
    (⟨m.1 0, by
      simpa only [Nat.succ_eq_add_one] using
        Nat.lt_succ_iff.mpr
          (generalBidegreeCoordinateZero_le_floor_div_of_mem_positiveRealWeightedBall
            ellM ellX R hellM_pos hell m.2)⟩,
      ⟨m.1 1, by
      simpa only [Nat.succ_eq_add_one] using
        Nat.lt_succ_iff.mpr
          (generalBidegreeCoordinateOne_le_floor_div_of_mem_positiveRealWeightedBall
            ellM ellX R hellM_pos hell m.2)⟩)
  have hf : Function.Injective f := by
    intro m n hmn
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    fin_cases k
    · change m.1 (0 : Fin 2) = n.1 (0 : Fin 2)
      have hzero := congrArg (fun p : Fin (⌊R / ellM⌋₊ + 1) ×
        Fin (⌊R / ellX⌋₊ + 1) => (p.1 : ℕ)) hmn
      simpa only [f] using hzero
    · change m.1 (1 : Fin 2) = n.1 (1 : Fin 2)
      have hone := congrArg (fun p : Fin (⌊R / ellM⌋₊ + 1) ×
        Fin (⌊R / ellX⌋₊ + 1) => (p.2 : ℕ)) hmn
      simpa only [f] using hone
  calc
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card =
        Fintype.card ↥(generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Fin (⌊R / ellM⌋₊ + 1) × Fin (⌊R / ellX⌋₊ + 1)) :=
      Fintype.card_le_of_injective f hf
    _ = (⌊R / ellM⌋₊ + 1) * (⌊R / ellX⌋₊ + 1) := by simp

/-- The finite family of horizontal lattice slices of the weighted triangle.
For a fixed second exponent `j`, its fiber is the interval of admissible
first exponents. -/
noncomputable def generalBidegreePositiveRealWeightedLatticeSlices
    (ellM ellX R : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (⌊R / ellX⌋₊ + 1)).sigma fun j =>
    Finset.range (⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1)

/-- The explicit floor sum counting the horizontal lattice slices of a
positive real weighted ball. -/
noncomputable def generalBidegreePositiveRealWeightedFloorSum
    (ellM ellX R : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (⌊R / ellX⌋₊ + 1),
    (⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1)

/-- Exact finite lattice-point formula for the positive real weighted ball.
This is the floor-sum form of the source's `N(R)`. -/
theorem card_generalBidegreePositiveRealWeightedBall_eq_floorSum
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hR : 0 ≤ R) :
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card =
      ∑ j ∈ Finset.range (⌊R / ellX⌋₊ + 1),
        (⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1) := by
  classical
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  calc
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card =
        (generalBidegreePositiveRealWeightedLatticeSlices ellM ellX R).card := by
      apply Finset.card_bij (fun m _ => Sigma.mk (m 1) (m 0))
      · intro m hm
        rw [generalBidegreePositiveRealWeightedLatticeSlices, Finset.mem_sigma]
        constructor
        · apply Finset.mem_range.mpr
          exact Nat.lt_succ_iff.mpr
            (generalBidegreeCoordinateOne_le_floor_div_of_mem_positiveRealWeightedBall
              ellM ellX R hellM_pos hell hm)
        · apply Finset.mem_range.mpr
          apply Nat.lt_succ_iff.mpr
          have hm_weight : generalBidegreeRealWeight ellM ellX m ≤ R :=
            (mem_generalBidegreePositiveRealWeightedBall_iff
              ellM ellX R hellM_pos hell m).mp hm
          have hfirst : (m 0 : ℝ) * ellM ≤ R - (m 1 : ℝ) * ellX := by
            rw [generalBidegreeRealWeight] at hm_weight
            linarith
          have hdiv : (m 0 : ℝ) ≤ (R - (m 1 : ℝ) * ellX) / ellM :=
            (le_div_iff₀ hellM_pos).mpr hfirst
          exact Nat.le_floor hdiv
      · intro m hm n hn hmn
        apply Finsupp.ext
        intro k
        fin_cases k
        · change m 0 = n 0
          have hzero := congrArg (fun p : Σ _ : ℕ, ℕ => p.2) hmn
          exact hzero
        · change m 1 = n 1
          have hone := congrArg (fun p : Σ _ : ℕ, ℕ => p.1) hmn
          exact hone
      · intro b hb
        rcases b with ⟨j, i⟩
        rw [generalBidegreePositiveRealWeightedLatticeSlices, Finset.mem_sigma] at hb
        rcases hb with ⟨hj, hi⟩
        have hjle : j ≤ ⌊R / ellX⌋₊ :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hR_div_ellX_nonneg : 0 ≤ R / ellX :=
          div_nonneg hR hellX_pos.le
        have hjdiv : (j : ℝ) ≤ R / ellX :=
          (Nat.le_floor_iff hR_div_ellX_nonneg).mp hjle
        have hjmul : (j : ℝ) * ellX ≤ R :=
          (le_div_iff₀ hellX_pos).mp hjdiv
        have hres_nonneg : 0 ≤ R - (j : ℝ) * ellX := by linarith
        have hile : i ≤ ⌊(R - (j : ℝ) * ellX) / ellM⌋₊ :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hres_div_nonneg : 0 ≤ (R - (j : ℝ) * ellX) / ellM :=
          div_nonneg hres_nonneg hellM_pos.le
        have hidiv : (i : ℝ) ≤ (R - (j : ℝ) * ellX) / ellM :=
          (Nat.le_floor_iff hres_div_nonneg).mp hile
        have himul : (i : ℝ) * ellM ≤ R - (j : ℝ) * ellX :=
          (le_div_iff₀ hellM_pos).mp hidiv
        let m : generalBidegreeWeightedMonomialIndex :=
          Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j
        have hmzero : m 0 = i := by simp [m]
        have hmone : m 1 = j := by simp [m]
        have hm_weight : generalBidegreeRealWeight ellM ellX m ≤ R := by
          rw [generalBidegreeRealWeight, hmzero, hmone]
          linarith
        have hm : m ∈ generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell :=
          (mem_generalBidegreePositiveRealWeightedBall_iff
            ellM ellX R hellM_pos hell m).mpr hm_weight
        refine ⟨m, hm, ?_⟩
        simp only [hmzero, hmone]
    _ = ∑ j ∈ Finset.range (⌊R / ellX⌋₊ + 1),
          (⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1) := by
      simp only [generalBidegreePositiveRealWeightedLatticeSlices,
        Finset.card_sigma, Finset.card_range]

/-- Named version of the exact floor-sum formula, convenient for composing
with rank inequalities. -/
theorem card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hR : 0 ≤ R) :
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card =
      generalBidegreePositiveRealWeightedFloorSum ellM ellX R := by
  exact card_generalBidegreePositiveRealWeightedBall_eq_floorSum
    ellM ellX R hellM_pos hell hR

/-- The source-shaped weighted rank cap expressed entirely through explicit
finite floor sums, provided the shifted radius is nonnegative. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_floorSum_sub
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
      generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
        generalBidegreePositiveRealWeightedFloorSum ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hR : 0 ≤ R := by linarith
  calc
    generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX
            (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card :=
      generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
        A B ellM ellX R hellM_pos hell
    _ = generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
          generalBidegreePositiveRealWeightedFloorSum ellM ellX
            (R - ((A + 1 : ℕ) : ℝ) * ellX) := by
      rw [card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
            ellM ellX R hellM_pos hell hR,
        card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
          ellM ellX (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift]

/-- Combining the weighted kernel bound with the rectangle count yields an
explicit floor bound for the coefficient-evaluation rank. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_rectangle
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
      (⌊R / ellM⌋₊ + 1) * (⌊R / ellX⌋₊ + 1) := by
  calc
    generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX
            (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card :=
      generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
        A B ellM ellX R hellM_pos hell
    _ ≤ (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card :=
      Nat.sub_le _ _
    _ ≤ (⌊R / ellM⌋₊ + 1) * (⌊R / ellX⌋₊ + 1) :=
      card_generalBidegreePositiveRealWeightedBall_le_rectangle
        ellM ellX R hellM_pos hell

end PellPaper
