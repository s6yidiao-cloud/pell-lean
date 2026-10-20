import Pell.GeneralBidegreePositiveRealWeightedRank
import Mathlib.Tactic

/-!
# The exact two-row rank cap for the two-layer coefficient grid

For `A = 1`, multiplication by the parallel-line relation removes precisely
the coefficient monomials whose second exponent is at least two.  This module
identifies the resulting cardinality defect with the literal weighted ball
in the two normal-form rows `j = 0,1`, and hence bounds the coefficient-
evaluation rank by that two-row count.
-/

namespace PellPaper

open Finset

noncomputable section

/-- The portion of a positive real weighted ball in the normal-form rows
`j = 0,1`. -/
def twoLayerNormalRowPositiveRealWeightedBall
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    Finset generalBidegreeCoefficientMonomialIndex :=
  (generalBidegreePositiveRealWeightedBall
    ellM ellX R hellM_pos hell).filter fun m => m 1 ≤ 1

/-- The complementary part of the weighted ball, whose second exponent is
at least two. -/
def twoLayerHighRowPositiveRealWeightedBall
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    Finset generalBidegreeCoefficientMonomialIndex :=
  (generalBidegreePositiveRealWeightedBall
    ellM ellX R hellM_pos hell).filter fun m => 2 ≤ m 1

/-- Shift a coefficient monomial upward by two in its second exponent. -/
def twoLayerShiftSecondExponentTwo
    (m : generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeCoefficientMonomialIndex :=
  m + Finsupp.single (1 : Fin 2) 2

@[simp]
theorem twoLayerShiftSecondExponentTwo_zero
    (m : generalBidegreeCoefficientMonomialIndex) :
    twoLayerShiftSecondExponentTwo m 0 = m 0 := by
  simp [twoLayerShiftSecondExponentTwo]

@[simp]
theorem twoLayerShiftSecondExponentTwo_one
    (m : generalBidegreeCoefficientMonomialIndex) :
    twoLayerShiftSecondExponentTwo m 1 = m 1 + 2 := by
  simp [twoLayerShiftSecondExponentTwo]

theorem generalBidegreeRealWeight_twoLayerShiftSecondExponentTwo
    (ellM ellX : ℝ) (m : generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeRealWeight ellM ellX
        (twoLayerShiftSecondExponentTwo m) =
      generalBidegreeRealWeight ellM ellX m + 2 * ellX := by
  simp [generalBidegreeRealWeight, twoLayerShiftSecondExponentTwo]
  ring

/-- Lower the second exponent by two, retaining both coordinates explicitly
on the two-element variable type. -/
def twoLayerUnshiftSecondExponentTwo
    (m : generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeCoefficientMonomialIndex :=
  Finsupp.single (0 : Fin 2) (m 0) +
    Finsupp.single (1 : Fin 2) (m 1 - 2)

@[simp]
theorem twoLayerUnshiftSecondExponentTwo_zero
    (m : generalBidegreeCoefficientMonomialIndex) :
    twoLayerUnshiftSecondExponentTwo m 0 = m 0 := by
  simp [twoLayerUnshiftSecondExponentTwo]

@[simp]
theorem twoLayerUnshiftSecondExponentTwo_one
    (m : generalBidegreeCoefficientMonomialIndex) :
    twoLayerUnshiftSecondExponentTwo m 1 = m 1 - 2 := by
  simp [twoLayerUnshiftSecondExponentTwo]

theorem twoLayerShift_unshiftSecondExponentTwo
    (m : generalBidegreeCoefficientMonomialIndex) (hm : 2 ≤ m 1) :
    twoLayerShiftSecondExponentTwo (twoLayerUnshiftSecondExponentTwo m) = m := by
  apply Finsupp.ext
  intro q
  fin_cases q
  · simp
  · simp [Nat.sub_add_cancel hm]

theorem twoLayerUnshift_shiftSecondExponentTwo
    (m : generalBidegreeCoefficientMonomialIndex) :
    twoLayerUnshiftSecondExponentTwo (twoLayerShiftSecondExponentTwo m) = m := by
  apply Finsupp.ext
  intro q
  fin_cases q
  · simp
  · simp

/-- Shifting by two gives a cardinality-preserving correspondence between
the ball of radius `R - 2 ellX` and the high-row part of the radius-`R`
ball.  This identity is valid even when the smaller ball is empty. -/
theorem card_positiveRealWeightedBall_shiftedTwo_eq_highRow
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    (generalBidegreePositiveRealWeightedBall ellM ellX
      (R - 2 * ellX) hellM_pos hell).card =
      (twoLayerHighRowPositiveRealWeightedBall
        ellM ellX R hellM_pos hell).card := by
  classical
  apply Finset.card_bij
    (fun m _ => twoLayerShiftSecondExponentTwo m)
  · intro m hm
    rw [twoLayerHighRowPositiveRealWeightedBall, Finset.mem_filter]
    constructor
    · rw [mem_generalBidegreePositiveRealWeightedBall_iff]
      rw [generalBidegreeRealWeight_twoLayerShiftSecondExponentTwo]
      have hmweight := (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX (R - 2 * ellX) hellM_pos hell m).mp hm
      linarith
    · simp
  · intro m hm n hn hmn
    have := congrArg twoLayerUnshiftSecondExponentTwo hmn
    calc
      m = twoLayerUnshiftSecondExponentTwo
          (twoLayerShiftSecondExponentTwo m) :=
        (twoLayerUnshift_shiftSecondExponentTwo m).symm
      _ = twoLayerUnshiftSecondExponentTwo
          (twoLayerShiftSecondExponentTwo n) := this
      _ = n := twoLayerUnshift_shiftSecondExponentTwo n
  · intro n hn
    rw [twoLayerHighRowPositiveRealWeightedBall, Finset.mem_filter] at hn
    rcases hn with ⟨hnball, hnhigh⟩
    let m := twoLayerUnshiftSecondExponentTwo n
    have hmweight : generalBidegreeRealWeight ellM ellX m ≤
        R - 2 * ellX := by
      have hnweight := (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX R hellM_pos hell n).mp hnball
      dsimp [m]
      rw [generalBidegreeRealWeight]
      simp only [twoLayerUnshiftSecondExponentTwo_zero,
        twoLayerUnshiftSecondExponentTwo_one]
      have hcast : ((n 1 - 2 : ℕ) : ℝ) = (n 1 : ℝ) - 2 := by
        rw [Nat.cast_sub hnhigh]
        norm_num
      rw [hcast]
      rw [generalBidegreeRealWeight] at hnweight
      nlinarith
    have hm : m ∈ generalBidegreePositiveRealWeightedBall ellM ellX
        (R - 2 * ellX) hellM_pos hell :=
      (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX (R - 2 * ellX) hellM_pos hell m).mpr hmweight
    refine ⟨m, hm, ?_⟩
    exact twoLayerShift_unshiftSecondExponentTwo n hnhigh

/-- The parallel-line cardinality defect at `A = 1` is exactly the number
of admissible normal-row monomials. -/
theorem card_positiveRealWeightedBall_sub_shiftedTwo_eq_normalRow
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    (generalBidegreePositiveRealWeightedBall
        ellM ellX R hellM_pos hell).card -
      (generalBidegreePositiveRealWeightedBall ellM ellX
        (R - 2 * ellX) hellM_pos hell).card =
      (twoLayerNormalRowPositiveRealWeightedBall
        ellM ellX R hellM_pos hell).card := by
  classical
  let U := generalBidegreePositiveRealWeightedBall
    ellM ellX R hellM_pos hell
  let L := twoLayerNormalRowPositiveRealWeightedBall
    ellM ellX R hellM_pos hell
  let H := twoLayerHighRowPositiveRealWeightedBall
    ellM ellX R hellM_pos hell
  have hpartition : L.card + H.card = U.card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := U) (p := fun m => m 1 ≤ 1)
    have hnot : (U.filter fun m => ¬m 1 ≤ 1) = H := by
      ext m
      simp [H, U, twoLayerHighRowPositiveRealWeightedBall]
      omega
    change (U.filter fun m => m 1 ≤ 1).card + H.card = U.card
    rw [← hnot]
    exact hfilter
  have hshift := card_positiveRealWeightedBall_shiftedTwo_eq_highRow
    ellM ellX R hellM_pos hell
  dsimp [U, L, H] at hpartition ⊢
  omega

/-- Exact normal-row cap for the coefficient-evaluation rank on
`Gamma_(1,B)`. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_twoLayerNormalRows
    (B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank 1 B
      (generalBidegreePositiveRealWeightedBall
        ellM ellX R hellM_pos hell) ≤
      (twoLayerNormalRowPositiveRealWeightedBall
        ellM ellX R hellM_pos hell).card := by
  calc
    generalBidegreeCoefficientEvaluationRank 1 B
        (generalBidegreePositiveRealWeightedBall
          ellM ellX R hellM_pos hell) ≤
        (generalBidegreePositiveRealWeightedBall
          ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX
            (R - ((1 + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card :=
      generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
        1 B ellM ellX R hellM_pos hell
    _ = (twoLayerNormalRowPositiveRealWeightedBall
          ellM ellX R hellM_pos hell).card := by
      norm_num
      exact card_positiveRealWeightedBall_sub_shiftedTwo_eq_normalRow
        ellM ellX R hellM_pos hell

end

end PellPaper
