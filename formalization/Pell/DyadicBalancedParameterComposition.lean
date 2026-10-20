import Pell.DyadicBalancedActualCellAggregation
import Pell.DyadicSourceTargetCellAuxiliaryForm
import Pell.DyadicResidualFullCellBudget

/-!
# Composing local auxiliary forms and full-cell budgets

This draft feeds the determinant-method two-layer form on each source-ratio
cell, together with the explicit uniform residual-sieve threshold, into the
actual-cell thin/full aggregation theorem.  It removes the abstract cellwise
form package while leaving the numerical determinant and threshold
inequalities explicit.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The exact Hadamard height of the source-degree-one auxiliary form at
actual rank `r`. -/
def dyadicSourceTargetCellAuxiliaryHeight
    (B r : ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (√(r : ℝ) *
    (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
      (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r

/-- A full-column-count Hadamard height that works for every actual rank
`r < 2(B+1)`.  This is the same uniform scale used by the generic two-layer
Hadamard endpoint. -/
def dyadicSourceTargetCellAuxiliaryUniformHeight
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (√((2 * (B + 1) : ℕ) : ℝ) *
    (((dyadicSourceCoordinateBound i : ℤ) ^ 1 *
      (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^
        (2 * (B + 1))

/-- The uniform auxiliary height is nonnegative. -/
theorem dyadicSourceTargetCellAuxiliaryUniformHeight_nonneg
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    0 ≤ dyadicSourceTargetCellAuxiliaryUniformHeight B i := by
  rw [dyadicSourceTargetCellAuxiliaryUniformHeight]
  positivity

/-- Every admissible actual-rank height is bounded by the full-column-count
Hadamard height. -/
theorem dyadicSourceTargetCellAuxiliaryHeight_le_uniform
    (B r : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (hr : r < 2 * (B + 1)) :
    dyadicSourceTargetCellAuxiliaryHeight B r i ≤
      dyadicSourceTargetCellAuxiliaryUniformHeight B i := by
  let S : ℤ := dyadicSourceCoordinateBound i
  let T : ℤ := dyadicTargetCoordinateBound i
  have hSNat : 1 ≤ dyadicSourceCoordinateBound i := by
    rw [dyadicSourceCoordinateBound]
    have hpow : 1 ≤ 2 ^ i.1 := one_le_pow₀ (by norm_num)
    have hmax : 1 ≤ max (2 ^ i.1) (2 ^ i.2.1) :=
      hpow.trans (Nat.le_max_left _ _)
    omega
  have hTNat : 1 ≤ dyadicTargetCoordinateBound i := by
    rw [dyadicTargetCoordinateBound]
    have hpow : 1 ≤ 2 ^ i.2.2.1 := one_le_pow₀ (by norm_num)
    have hmax : 1 ≤ max (2 ^ i.2.2.1) (2 ^ i.2.2.2) :=
      hpow.trans (Nat.le_max_left _ _)
    omega
  have hS : (1 : ℤ) ≤ S := by dsimp [S]; exact_mod_cast hSNat
  have hT : (1 : ℤ) ≤ T := by dsimp [T]; exact_mod_cast hTNat
  have hrle : r ≤ 2 * (B + 1) := Nat.le_of_lt hr
  have hTpow : (1 : ℤ) ≤ T ^ B := one_le_pow₀ hT
  have hqInt : (1 : ℤ) ≤ S ^ 1 * T ^ B := by
    simpa only [pow_one, one_mul] using
      mul_le_mul hS hTpow (by norm_num) (zero_le_one.trans hS)
  have hq : (1 : ℝ) ≤ (((S ^ 1 * T ^ B : ℤ) : ℝ)) := by
    exact_mod_cast hqInt
  have hqnonneg : (0 : ℝ) ≤ (((S ^ 1 * T ^ B : ℤ) : ℝ)) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans hq
  have hcardOne : (1 : ℝ) ≤ (2 * (B + 1) : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * (B + 1) by omega)
  have hsqrtCardOne :
      (1 : ℝ) ≤ √((2 * (B + 1) : ℕ) : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hcardOne
  have hsqrtrle :
      √(r : ℝ) ≤ √((2 * (B + 1) : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hrle
  have hbase :
      √(r : ℝ) * (((S ^ 1 * T ^ B : ℤ) : ℝ)) ≤
        √((2 * (B + 1) : ℕ) : ℝ) *
          (((S ^ 1 * T ^ B : ℤ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hsqrtrle hqnonneg
  have hbaseOne :
      (1 : ℝ) ≤ √((2 * (B + 1) : ℕ) : ℝ) *
        (((S ^ 1 * T ^ B : ℤ) : ℝ)) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ √((2 * (B + 1) : ℕ) : ℝ) *
          (((S ^ 1 * T ^ B : ℤ) : ℝ)) :=
        mul_le_mul hsqrtCardOne hq (by norm_num) (Real.sqrt_nonneg _)
  rw [dyadicSourceTargetCellAuxiliaryHeight,
    dyadicSourceTargetCellAuxiliaryUniformHeight]
  change
    (√(r : ℝ) * (((S ^ 1 * T ^ B : ℤ) : ℝ))) ^ r ≤
      (√((2 * (B + 1) : ℕ) : ℝ) *
        (((S ^ 1 * T ^ B : ℤ) : ℝ))) ^ (2 * (B + 1))
  exact
    (pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hqnonneg) hbase r).trans
      (pow_le_pow_right₀ hbaseOne hrle)

/-- The integer coefficient-height input required after factor extraction
from the common degree-`B` auxiliary height. -/
def dyadicSourceTargetCellResidualHeight
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  positiveNatCeil
    ((2 : ℝ) ^ B * ((B : ℝ) + 1) *
      dyadicSourceTargetCellAuxiliaryUniformHeight B i)

/-- **Determinant-to-aggregation composition.**  The existing polynomial-mesh
determinant endpoint supplies a possibly different form (and actual rank) for
each source cell.  A threshold inequality uniform over every admissible rank
then supplies all residual full-cell budgets, so the canonical actual-cell
aggregation applies.

This statement does not prove the displayed determinant or threshold
inequalities; it exposes exactly the numerical obligations that remain. -/
theorem eventually_dyadicFactorBoxCell_card_le_thinFull_of_polynomialMesh_and_uniformBudget
    (hWeil : OneVariableQuadraticWeilDegreeBound) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (B H0 : ℕ) (theta Q : ℝ) (Y : ℕ)
        (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
        (xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
          quadCoeff meshCoeff : ℝ),
        0 < M → 2 ≤ Y → 2 ≤ Q →
        (M : ℝ) ≤
          ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (2 * Q) →
        xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
          ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        1536 ≤ xScale → 0 < sigma →
        Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale →
        m * L ≤ Real.log (M : ℝ) →
        xDet * L = (1 - sigma) * Real.log xScale →
        0 < B → 0 < m → m ≤ xDet →
        xDet * ((1 : ℝ) / (B : ℝ)) ≤ 2 * m →
        L = Real.log (Y : ℝ) →
        0 < gainCoeff → 0 ≤ quadCoeff → 0 < slack →
        Real.exp (shearedComparableCoordinateLogLoss 1 B 2 24 / slack) ≤
          (Y : ℝ) →
        ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
            (1 * ((1 + 1) * (B + 1)) / 2) *
          ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
            (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
              (B * ((1 + 1) * (B + 1)) / 2) ≤ Real.exp baseCost →
        baseCost + slack * L +
          Real.log
              (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
            shearedActualRankTaylorTail 1 B *
              (Fintype.card (generalBidegreeGrid 1 B) : ℝ) ≤
          sourceNormalizedLeadingCost B ((1 : ℝ) / (B : ℝ))
              alphaDE alphaUV L +
            quadCoeff * (B : ℝ) ^ 2 * L →
        quadCoeff * (B : ℝ) ^ 2 ≤
          (gainCoeff / 2) * (B : ℝ) ^ 3 →
        sourceNormalizedFloorPolynomialMeshCorrection 1 B m xDet L ≤
          meshCoeff * (B : ℝ) ^ 3 * L →
        gainCoeff + meshCoeff ≤
          shearedSurplus m xDet alphaDE alphaUV ((1 : ℝ) / (B : ℝ)) →
        fullCellResidualSieveUniformBudgetThreshold i M B
            (dyadicSourceTargetCellResidualHeight B i) ≤ (N : ℝ) →
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            8 * fullCellOddDegreeSieveAggregateEnvelope
              N (2 * B + 1) U V (M : ℝ) := by
  filter_upwards
    [eventually_dyadicFactorBoxCell_card_le_thinFull_of_cellwiseAuxiliary
      hWeil] with N haggregate
  intro B H0 theta Q Y i M xScale sigma m xDet L baseCost slack
    alphaDE alphaUV gainCoeff quadCoeff meshCoeff hM hY hQ hMscale hxQ
    htargetScale hxScale hsigma hlocalThreshold hsourceDecay hxDetL hB hm
    hmxDet hshear hL hgain hquad hslack hcomparisonThreshold hbaseCost
    hbudget hdominates hpolynomialMeshCorrection hcontinuousSurplus
    hthreshold
  dsimp only
  apply haggregate B H0 theta Q Y i M hM hY hQ hMscale hxQ
  intro p _hp _hoccupancy
  obtain ⟨r, hr, f, hf0, hvanish, hheight⟩ :=
    exists_nonzero_real_bounded_integral_twoLayerForm_of_dyadicSourceTargetTupleCell_uniformDyadicComparableCostPolynomialMeshRate
      B hM xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
        quadCoeff meshCoeff htargetScale hxScale hsigma hlocalThreshold
          hsourceDecay hxDetL hB hm hmxDet hshear hL
            (by exact_mod_cast hY) hgain hquad hslack hcomparisonThreshold
              hbaseCost hbudget hdominates hpolynomialMeshCorrection
                hcontinuousSurplus
  refine ⟨f, dyadicSourceTargetCellAuxiliaryUniformHeight B i, hf0, ?_, ?_, ?_, ?_⟩
  · exact dyadicSourceTargetCellAuxiliaryUniformHeight_nonneg B i
  · intro ab
    exact (hheight ab).trans
      (dyadicSourceTargetCellAuxiliaryHeight_le_uniform B r i hr)
  · exact hvanish p.2
  · intro _hfull
    apply fullCellResidualSieveBudgets_of_uniformBudgetThreshold_le
    exact hthreshold

end

end PellPaper
