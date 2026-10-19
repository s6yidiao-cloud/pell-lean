import Pell.DyadicComparableCostPolynomialMeshFiniteCellHeight
import Pell.FiniteCellSparsity

/-!
# Actual dyadic factor cells for the polynomial-mesh auxiliary form

This module packages one box of the finite separated factor family as its
literal homogeneous point cell.  The coordinate map is injective, so the
point cell has exactly the original tuple-cell cardinality.  The quantitative
determinant hypotheses are intentionally not supplied here.
-/

namespace PellPaper

noncomputable section

/-- The literal homogeneous-coordinate map from a factor tuple to the
source/target point `((d,e),(v,u))`. -/
def dyadicFactorTupleToGeneralBidegreeFormPointEmbedding :
    (ℕ × ℕ × ℕ × ℕ) ↪ GeneralBidegreeFormPoint where
  toFun := dyadicFactorTupleToGeneralBidegreeFormPoint
  inj' := by
    rintro ⟨d, e, u, v⟩ ⟨d', e', u', v'⟩ h
    have hd := congrArg (fun p : GeneralBidegreeFormPoint => p.1.1) h
    have he := congrArg (fun p : GeneralBidegreeFormPoint => p.1.2) h
    have hu := congrArg (fun p : GeneralBidegreeFormPoint => p.2.2) h
    have hv := congrArg (fun p : GeneralBidegreeFormPoint => p.2.1) h
    simp only [dyadicFactorTupleToGeneralBidegreeFormPoint] at hd he hu hv
    have hd' : d = d' := by exact_mod_cast hd
    have he' : e = e' := by exact_mod_cast he
    have hu' : u = u' := by exact_mod_cast hu
    have hv' : v = v' := by exact_mod_cast hv
    subst d'
    subst e'
    subst u'
    subst v'
    rfl

/-- The actual integral homogeneous points of a finite factor-tuple family. -/
noncomputable def dyadicFactorTuplePointCell
    (S : Finset (ℕ × ℕ × ℕ × ℕ)) : Finset GeneralBidegreeFormPoint :=
  S.map dyadicFactorTupleToGeneralBidegreeFormPointEmbedding

/-- A point of a mapped factor-tuple cell has a chosen original tuple. -/
noncomputable def dyadicFactorTuplePointCellPreimage
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (p : {q // q ∈ dyadicFactorTuplePointCell S}) : ℕ × ℕ × ℕ × ℕ :=
  Classical.choose (Finset.mem_map.mp p.2)

/-- The chosen preimage lies in the original finite tuple family. -/
theorem dyadicFactorTuplePointCellPreimage_mem
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (p : {q // q ∈ dyadicFactorTuplePointCell S}) :
    dyadicFactorTuplePointCellPreimage S p ∈ S := by
  exact (Classical.choose_spec (Finset.mem_map.mp p.2)).1

/-- Mapping the chosen tuple recovers the displayed homogeneous point. -/
theorem dyadicFactorTuplePointCellPreimage_map_eq
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (p : {q // q ∈ dyadicFactorTuplePointCell S}) :
    dyadicFactorTupleToGeneralBidegreeFormPoint
      (dyadicFactorTuplePointCellPreimage S p) = p.1 := by
  exact (Classical.choose_spec (Finset.mem_map.mp p.2)).2

/-- The actual integral homogeneous points of one dyadic factor box. -/
noncomputable def dyadicFactorBoxPointCell (theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) : Finset GeneralBidegreeFormPoint :=
  dyadicFactorTuplePointCell (dyadicFactorBoxCell theta Y i)

/-- The homogeneous point cell retains the exact cardinality of its factor
tuple cell. -/
@[simp] theorem card_dyadicFactorBoxPointCell (theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) :
    (dyadicFactorBoxPointCell theta Y i).card =
      (dyadicFactorBoxCell theta Y i).card := by
  simp [dyadicFactorBoxPointCell, dyadicFactorTuplePointCell]

/-- **Actual dyadic-factor-cell auxiliary form with literal height.**  The
finite cell is no longer an abstract set of homogeneous points: it is exactly
the image of one bounded factor box under `((d,e),(v,u))`.  Thus box
membership and the factor condition are recovered internally for every cell
point, and only the common local source window and global quantitative
determinant hypotheses remain supplied.

This proves neither those source hypotheses nor any factor/curve point count. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_dyadicFactorBoxCell_uniformDyadicComparableCostPolynomialMeshRate
    (A B : ℕ) {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
      quadCoeff meshCoeff : ℝ)
    (hwindow : ∀ q ∈ dyadicFactorBoxCell theta Y i,
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
        (∀ p ∈ dyadicFactorBoxPointCell theta Y i,
          generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound i : ℤ) ^ A *
                (dyadicTargetCoordinateBound i : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  let tuple : {p // p ∈ dyadicFactorBoxPointCell theta Y i} →
      ℕ × ℕ × ℕ × ℕ := fun p =>
    dyadicFactorTuplePointCellPreimage (dyadicFactorBoxCell theta Y i) p
  let d : {p // p ∈ dyadicFactorBoxPointCell theta Y i} → ℕ :=
    fun p => (tuple p).1
  let e : {p // p ∈ dyadicFactorBoxPointCell theta Y i} → ℕ :=
    fun p => (tuple p).2.1
  let u : {p // p ∈ dyadicFactorBoxPointCell theta Y i} → ℕ :=
    fun p => (tuple p).2.2.1
  let v : {p // p ∈ dyadicFactorBoxPointCell theta Y i} → ℕ :=
    fun p => (tuple p).2.2.2
  refine
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_finset_uniformDyadicComparableCostPolynomialMeshRate
      (theta := theta) (Y := Y) (i := i)
      A B (dyadicFactorBoxPointCell theta Y i) d e u v ?_
      s0 M xScale sigma m xDet L baseCost slack alphaDE alphaUV gainCoeff
        quadCoeff meshCoeff ?_ ?_ hs0 hM ?_ ?_ htargetScale hxScale hsigma
          hlocalThreshold hsourceDecay hxDetL hB hm hmxDet hshear hL hY hgain
            hquad hslack hcomparisonThreshold hbaseCost hbudget hdominates
              hpolynomialMeshCorrection hcontinuousSurplus
  · intro p
    change dyadicFactorTupleToGeneralBidegreeFormPoint
      (d p, e p, u p, v p) = p.1
    simpa [d, e, u, v, tuple] using
      dyadicFactorTuplePointCellPreimage_map_eq
        (dyadicFactorBoxCell theta Y i) p
  · intro p
    have hp := dyadicFactorTuplePointCellPreimage_mem
      (dyadicFactorBoxCell theta Y i) p
    exact mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hp).1
  · intro p
    have hp := dyadicFactorTuplePointCellPreimage_mem
      (dyadicFactorBoxCell theta Y i) p
    exact (Finset.mem_inter.mp hp).2
  · intro p
    have hp := dyadicFactorTuplePointCellPreimage_mem
      (dyadicFactorBoxCell theta Y i) p
    simpa [d, e, tuple] using (hwindow (tuple p) hp).1
  · intro p
    have hp := dyadicFactorTuplePointCellPreimage_mem
      (dyadicFactorBoxCell theta Y i) p
    simpa [d, e, tuple] using (hwindow (tuple p) hp).2

end

end PellPaper
