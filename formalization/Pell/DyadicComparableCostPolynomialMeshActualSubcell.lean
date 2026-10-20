import Pell.DyadicComparableCostPolynomialMeshActualCell

/-!
# Uniform polynomial-mesh forms on actual dyadic subcells

The determinant endpoint applies to any finite subcell of a dyadic factor box
once its common source-ratio window is supplied.  This module transports the
actual tuple/factor/box data to that generic endpoint without requiring the
subcell to equal the whole box.  It is the adapter needed for an explicit
local-ratio partition.

No local cover, determinant budget, factor analysis, or point-counting result
is asserted here.
-/

namespace PellPaper

noncomputable section

/-- **Actual dyadic-subcell auxiliary form with literal height.**  A finite
subcell of one dyadic factor box maps by `((d,e),(v,u))` to its literal
homogeneous point set.  The subcell hypothesis recovers all factor and box
data for the generic finite-cell endpoint; its common local source window and
all quantitative determinant hypotheses remain explicit. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_dyadicFactorTupleSubcell_uniformDyadicComparableCostPolynomialMeshRate
    (A B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hS : S ⊆ dyadicFactorBoxCell theta Y i)
    (s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
      quadCoeff meshCoeff : ℝ)
    (hwindow : ∀ q ∈ S,
      s0 ≤ (q.1 : ℝ) / (q.2.1 : ℝ) ∧
        (q.1 : ℝ) / (q.2.1 : ℝ) ≤ s0 * (1 + 1 / M))
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (htargetScale : xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log M)
    (hxDetL : xDet * L = (1 - sigma) * Real.log xScale)
    (hB : 0 < B) (hm : 0 < m) (hmxDet : m ≤ xDet)
    (hshear : xDet * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hL : L = Real.log (Y : ℝ)) (hY : 1 < (Y : ℝ))
    (hgain : 0 < gainCoeff) (hquad : 0 ≤ quadCoeff) (hslack : 0 < slack)
    (hcomparisonThreshold :
      Real.exp (shearedComparableCoordinateLogLoss A B 2 24 / slack) ≤ (Y : ℝ))
    (hbaseCost :
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (A * ((A + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
            (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp baseCost)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
        shearedActualRankTaylorTail A B *
          (Fintype.card (generalBidegreeGrid A B) : ℝ) ≤
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hpolynomialMeshCorrection :
      sourceNormalizedFloorPolynomialMeshCorrection A B m xDet L ≤
        meshCoeff * (B : ℝ) ^ 3 * L)
    (hcontinuousSurplus : gainCoeff + meshCoeff ≤
      shearedSurplus m xDet alphaDE alphaUV ((A : ℝ) / (B : ℝ))) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ dyadicFactorTuplePointCell S,
          generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  let tuple : {p // p ∈ dyadicFactorTuplePointCell S} →
      ℕ × ℕ × ℕ × ℕ := fun p =>
    dyadicFactorTuplePointCellPreimage S p
  let d : {p // p ∈ dyadicFactorTuplePointCell S} → ℕ :=
    fun p => (tuple p).1
  let e : {p // p ∈ dyadicFactorTuplePointCell S} → ℕ :=
    fun p => (tuple p).2.1
  let u : {p // p ∈ dyadicFactorTuplePointCell S} → ℕ :=
    fun p => (tuple p).2.2.1
  let v : {p // p ∈ dyadicFactorTuplePointCell S} → ℕ :=
    fun p => (tuple p).2.2.2
  refine
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_finset_uniformDyadicComparableCostPolynomialMeshRate
      (theta := theta) (Y := Y) (i := i)
      A B (dyadicFactorTuplePointCell S) d e u v ?_
      s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
        quadCoeff meshCoeff ?_ ?_ hs0 hM ?_ ?_ htargetScale hxScale hsigma
          hlocalThreshold hsourceDecay hxDetL hB hm hmxDet hshear hL hY hgain
            hquad hslack hcomparisonThreshold hbaseCost hbudget hdominates
              hpolynomialMeshCorrection hcontinuousSurplus
  · intro p
    change dyadicFactorTupleToGeneralBidegreeFormPoint
      (d p, e p, u p, v p) = p.1
    simpa [d, e, u, v, tuple] using
      dyadicFactorTuplePointCellPreimage_map_eq S p
  · intro p
    have hpS := dyadicFactorTuplePointCellPreimage_mem S p
    have hpbox := hS hpS
    exact mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hpbox).1
  · intro p
    have hpS := dyadicFactorTuplePointCellPreimage_mem S p
    have hpbox := hS hpS
    exact (Finset.mem_inter.mp hpbox).2
  · intro p
    have hpS := dyadicFactorTuplePointCellPreimage_mem S p
    simpa [d, e, tuple] using (hwindow (tuple p) hpS).1
  · intro p
    have hpS := dyadicFactorTuplePointCellPreimage_mem S p
    simpa [d, e, tuple] using (hwindow (tuple p) hpS).2

/-- Homogeneous vanishing on the mapped point cell of an actual subcell
returns to affine vanishing at each original tuple coordinate `(d/e,v/u)`.
The ambient-box containment supplies only the factor-family denominator facts. -/
theorem generalBidegreeFormAffineEval_eq_zero_of_vanishing_on_dyadicFactorTuplePointSubcell
    (A B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hS : S ⊆ dyadicFactorBoxCell theta Y i)
    (c : generalBidegreeFormIndex A B → ℤ)
    (hvanish : ∀ p ∈ dyadicFactorTuplePointCell S,
      generalBidegreeFormEval A B c p = 0)
    {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ S) :
    generalBidegreeFormAffineEval A B c
      ((q.1 : ℚ) / (q.2.1 : ℚ))
      ((q.2.2.2 : ℚ) / (q.2.2.1 : ℚ)) = 0 := by
  apply generalBidegreeFormAffineEval_eq_zero_of_mem_dyadicFactorTuples
    A B c q (Finset.mem_inter.mp (hS hq)).1
  exact hvanish _ (Finset.mem_map.mpr ⟨q, hq, rfl⟩)

/-- A nonzero bounded homogeneous auxiliary form on an actual subcell yields
the same-degree, same-height affine relation on every tuple of that subcell.
It carries no factorization or rational-point-count assertion. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeFormAffine_of_vanishing_on_dyadicFactorTuplePointSubcell
    (A B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hS : S ⊆ dyadicFactorBoxCell theta Y i)
    (haux : ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ dyadicFactorTuplePointCell S,
          generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ q ∈ S,
          generalBidegreeFormAffineEval A B c
            ((q.1 : ℚ) / (q.2.1 : ℚ))
            ((q.2.2.2 : ℚ) / (q.2.2.1 : ℚ)) = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  rcases haux with ⟨r, hr, c, hc, hvanish, hheight⟩
  refine ⟨r, hr, c, hc, ?_, hheight⟩
  intro q hq
  exact generalBidegreeFormAffineEval_eq_zero_of_vanishing_on_dyadicFactorTuplePointSubcell
    A B S hS c hvanish hq

end

end PellPaper
