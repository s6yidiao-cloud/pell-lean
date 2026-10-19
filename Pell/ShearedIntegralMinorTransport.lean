import Pell.GeneralBidegreeAffineMinorTransport
import Pell.IntegralDeterminantVanishing
import Pell.ShearedCenterExponentFormula
import Pell.ShearedExponentialEvaluationMatrixAlignment

/-!
# Transport from a sheared determinant to an integral selected minor

This module isolates the exact final handoff in the rectangular determinant
method.  A source-specific row-denominator identity identifies a selected
integral minor, after real casting, with a row-scaled centred affine minor.
The existing centre extraction then expresses it through the reindexed sheared
exponential determinant.  A strict bound below one therefore forces the
integral selected minor to vanish.

The only source-specific input is the displayed matrix identity
`htransport`; it is deliberately explicit rather than asserted here.
-/

namespace PellPaper

open scoped BigOperators

/-- The source-oriented integral monomial obtained by clearing the
denominators of the affine source column `s^a t^b`.  Its column convention is
the reverse of `generalBidegreeFormMonomial`, whose standard homogeneous
index records the exponents of the denominator coordinates. -/
def sourceOrientedGeneralBidegreeFormMonomial (A B : ℕ)
    (p : GeneralBidegreeFormPoint) (ab : generalBidegreeFormIndex A B) : ℤ :=
  p.1.1 ^ ab.1.1 * p.1.2 ^ (A - ab.1.1) *
    p.2.1 ^ ab.2.1 * p.2.2 ^ (B - ab.2.1)

/-- The integral matrix obtained from the literal affine source columns
`s^a t^b` after clearing each row denominator by `e^A u^B`. -/
def sourceOrientedGeneralBidegreeClearedEvaluationMatrix {ι : Type*} (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex A B) ℤ :=
  fun row ab => sourceOrientedGeneralBidegreeFormMonomial A B (points row) ab

/-- Reversing both bounded coefficient coordinates exchanges the source
column convention `s^a t^b` with the standard homogeneous convention. -/
def generalBidegreeFormIndexReflection (A B : ℕ) :
    generalBidegreeFormIndex A B ≃ generalBidegreeFormIndex A B :=
  Equiv.prodCongr Fin.revPerm Fin.revPerm

/-- The reflected source exponent has the complementary standard exponent. -/
theorem sourceExponent_sub_indexReflection_eq
    (A B : ℕ) (ab : generalBidegreeFormIndex A B) :
    A - (generalBidegreeFormIndexReflection A B ab).1.1 = ab.1.1 := by
  change A - (Fin.rev ab.1).1 = ab.1.1
  have h := Fin.add_rev_cast ab.1
  omega

/-- The reflected source denominator exponent is the complementary source
exponent. -/
theorem indexReflection_sourceExponent_eq_sub
    (A B : ℕ) (ab : generalBidegreeFormIndex A B) :
    (generalBidegreeFormIndexReflection A B ab).1.1 = A - ab.1.1 := by
  change (Fin.rev ab.1).1 = A - ab.1.1
  have h := Fin.add_rev_cast ab.1
  omega

/-- The reflected target exponent has the complementary standard exponent. -/
theorem targetExponent_sub_indexReflection_eq
    (A B : ℕ) (ab : generalBidegreeFormIndex A B) :
    B - (generalBidegreeFormIndexReflection A B ab).2.1 = ab.2.1 := by
  change B - (Fin.rev ab.2).1 = ab.2.1
  have h := Fin.add_rev_cast ab.2
  omega

/-- The reflected target denominator exponent is the complementary target
exponent. -/
theorem indexReflection_targetExponent_eq_sub
    (A B : ℕ) (ab : generalBidegreeFormIndex A B) :
    (generalBidegreeFormIndexReflection A B ab).2.1 = B - ab.2.1 := by
  change (Fin.rev ab.2).1 = B - ab.2.1
  have h := Fin.add_rev_cast ab.2
  omega

/-- The source-oriented cleared evaluation matrix is the standard integral
evaluation matrix with its two coefficient coordinates reflected. -/
theorem sourceOrientedClearedEvaluationMatrix_eq_standard_columnReflection
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint) :
    sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points =
      (generalBidegreeFormEvaluationMatrix A B points).submatrix id
        (generalBidegreeFormIndexReflection A B) := by
  ext row ab
  simp only [sourceOrientedGeneralBidegreeClearedEvaluationMatrix,
    sourceOrientedGeneralBidegreeFormMonomial,
    generalBidegreeFormEvaluationMatrix, generalBidegreeFormMonomial,
    generalBidegreeFormSource, generalBidegreeFormTarget,
    Matrix.submatrix_apply, id_eq]
  rw [sourceExponent_sub_indexReflection_eq,
    indexReflection_sourceExponent_eq_sub,
    targetExponent_sub_indexReflection_eq,
    indexReflection_targetExponent_eq_sub]
  ring

/-- A single source-oriented cleared monomial is the row denominator factor
times the corresponding centred affine source monomial. -/
theorem cast_sourceOrientedGeneralBidegreeFormMonomial_eq_rowFactor_mul_affine
    (A B : ℕ) (d e v u : ℤ) (ab : generalBidegreeFormIndex A B)
    (he : (e : ℝ) ≠ 0) (hu : (u : ℝ) ≠ 0) :
    (sourceOrientedGeneralBidegreeFormMonomial A B ((d, e), (v, u)) ab : ℝ) =
      ((e : ℝ) ^ A * (u : ℝ) ^ B) *
        (((d : ℝ) / (e : ℝ)) ^ ab.1.1 * ((v : ℝ) / (u : ℝ)) ^ ab.2.1) := by
  have hA : A - ab.1.1 + ab.1.1 = A :=
    Nat.sub_add_cancel (generalBidegreeFormIndex_source_le A B ab)
  have hB : B - ab.2.1 + ab.2.1 = B :=
    Nat.sub_add_cancel (generalBidegreeFormIndex_target_le A B ab)
  have hepow : (e : ℝ) ^ (A - ab.1.1 + ab.1.1) = (e : ℝ) ^ A :=
    congrArg (fun n : ℕ => (e : ℝ) ^ n) hA
  have hupow : (u : ℝ) ^ (B - ab.2.1 + ab.2.1) = (u : ℝ) ^ B :=
    congrArg (fun n : ℕ => (u : ℝ) ^ n) hB
  simp only [sourceOrientedGeneralBidegreeFormMonomial, Int.cast_mul, Int.cast_pow]
  rw [← hepow, ← hupow, pow_add, pow_add, div_pow, div_pow]
  field_simp [he, hu]

/-- The literal denominator-clearing identity for source-oriented affine
columns.  Once the local coordinate equalities `d/e = s₀ S` and
`v/u = s₀² T` are supplied, no further source arithmetic is required. -/
theorem sourceOrientedClearedEvaluationMatrix_map_eq_rowScale_centeredAffine
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row) :
    (sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).map
      (Int.castRingHom ℝ) =
      rowScale (fun row =>
        ((points row).1.2 : ℝ) ^ A * ((points row).2.2 : ℝ) ^ B)
        (centeredAffineEvaluationMatrix A B s₀ S T) := by
  ext row ab
  rcases hpoint : points row with ⟨⟨d, e⟩, ⟨v, u⟩⟩
  have heZ : e ≠ 0 := by
    simpa [hpoint] using (hden row).1
  have huZ : u ≠ 0 := by
    simpa [hpoint] using (hden row).2
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast heZ
  have hu : (u : ℝ) ≠ 0 := by exact_mod_cast huZ
  have hs : (d : ℝ) / (e : ℝ) = s₀ * S row := by
    simpa [hpoint] using (hcoords row).1
  have ht : (v : ℝ) / (u : ℝ) = s₀ ^ 2 * T row := by
    simpa [hpoint] using (hcoords row).2
  simp only [Matrix.map_apply, sourceOrientedGeneralBidegreeClearedEvaluationMatrix,
    rowScale, centeredAffineEvaluationMatrix, affineMonomialEntry]
  rw [hpoint]
  change (sourceOrientedGeneralBidegreeFormMonomial A B ((d, e), (v, u)) ab : ℝ) =
    ((e : ℝ) ^ A * (u : ℝ) ^ B) *
      ((s₀ * S row) ^ ab.1.1 * (s₀ ^ 2 * T row) ^ ab.2.1)
  rw [cast_sourceOrientedGeneralBidegreeFormMonomial_eq_rowFactor_mul_affine
    A B d e v u ab he hu, hs, ht]

/-- Reindexing the source sheared matrix has the same determinant modulus as
the selected square minor whose rows are pulled back along the row and column
equivalences. -/
theorem abs_det_selectedShearedMinor_eq_abs_det_reindex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (E : Matrix ι (generalBidegreeFormIndex A B) ℝ) :
    let eCols := generalBidegreeGridPointEquiv A B
    let r : generalBidegreeFormIndex A B ≃ ι := eCols.trans eRows.symm
    |(E.submatrix r id).det| =
      |(Matrix.reindex eRows eCols E).det| := by
  dsimp only
  let eCols := generalBidegreeGridPointEquiv A B
  let r : generalBidegreeFormIndex A B ≃ ι := eCols.trans eRows.symm
  have hmatrix : Matrix.reindex eRows eCols E =
      Matrix.reindex eCols eCols (E.submatrix r id) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [r, Equiv.trans_apply]
    rw [eCols.apply_symm_apply i]
    rfl
  rw [hmatrix]
  exact (Matrix.abs_det_reindex eCols eCols (E.submatrix r id)).symm

/-- **Integral selected-minor transport.**  Suppose the real cast of a
selected integral minor is obtained by multiplying the centred affine minor
rowwise by explicit denominator factors.  If the resulting denominator,
centre, and reindexed sheared determinant product has modulus below one, then
the selected integral minor is zero.

The hypothesis `htransport` is the precise source-coordinate obligation: for
the intended integer matrix it must state the rowwise denominator-clearing
identity, including the (possibly reversed) column convention. -/
theorem selectedIntegralMinor_det_eq_zero_of_reindexedShearedTransport_abs_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (M : Matrix ι (generalBidegreeFormIndex A B) ℤ)
    (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ) (d : ι → ℝ)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (htransport :
      ((M.map (Int.castRingHom ℝ)).submatrix r id) =
        rowScale (fun i => d (r i))
          ((centeredAffineEvaluationMatrix A B s₀ S T).submatrix r id))
    (hsmall :
      |(∏ i : generalBidegreeFormIndex A B, d (r i)) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
            (shearedExponentialEvaluationMatrix A B S T)).det| < 1) :
    (M.submatrix r id).det = 0 := by
  have hreindex :
      |((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det| =
        |(Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
          (shearedExponentialEvaluationMatrix A B S T)).det| := by
    rw [hr]
    exact abs_det_selectedShearedMinor_eq_abs_det_reindex A B eRows
      (shearedExponentialEvaluationMatrix A B S T)
  have hdet :
      ((M.map (Int.castRingHom ℝ)).submatrix r id).det =
        (∏ i : generalBidegreeFormIndex A B, d (r i)) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          ((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det := by
    have hcenter :
        ((centeredAffineEvaluationMatrix A B s₀ S T).submatrix r id).det =
          (∏ ab : generalBidegreeFormIndex A B,
            shearedCenterColumnScale (A := A) (B := B) s₀ ab) *
            ((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det := by
      simpa only [Equiv.coe_toEmbedding] using
        (det_centeredAffineEvaluationMatrix_submatrix_eq_centerFactor_mul
          A B s₀ S T hS hT r.toEmbedding)
    calc
      ((M.map (Int.castRingHom ℝ)).submatrix r id).det =
          (rowScale (fun i => d (r i))
            ((centeredAffineEvaluationMatrix A B s₀ S T).submatrix r id)).det := by
              rw [htransport]
      _ = (∏ i : generalBidegreeFormIndex A B, d (r i)) *
          ((centeredAffineEvaluationMatrix A B s₀ S T).submatrix r id).det :=
        det_rowScale ℝ (fun i => d (r i))
          ((centeredAffineEvaluationMatrix A B s₀ S T).submatrix r id)
      _ = (∏ i : generalBidegreeFormIndex A B, d (r i)) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          ((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det := by
        rw [hcenter,
          prod_shearedCenterColumnScale_eq_card_mul_shearedDegree_div_two]
        ring
  have hsmall_selected :
      |(∏ i : generalBidegreeFormIndex A B, d (r i)) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          ((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det| < 1 := by
    have h := hsmall
    simp only [abs_mul] at h ⊢
    rw [← hreindex] at h
    exact h
  have hcast : |((M.submatrix r id).det : ℝ)| < 1 := by
    calc
      |((M.submatrix r id).det : ℝ)| =
          |((M.submatrix r id).map (Int.castRingHom ℝ)).det| := by
            simpa using congrArg abs
              (Int.cast_det (R := ℝ) (M.submatrix r id))
      _ = |((M.map (Int.castRingHom ℝ)).submatrix r id).det| := by
            rw [Matrix.submatrix_map]
      _ = |(∏ i : generalBidegreeFormIndex A B, d (r i)) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          ((shearedExponentialEvaluationMatrix A B S T).submatrix r id).det| := by
            rw [hdet]
      _ < 1 := hsmall_selected
  exact integral_det_eq_zero_of_abs_cast_lt_one (M.submatrix r id) hcast

/-- The preceding transport specialized to the literal source-oriented
denominator-cleared matrix.  Thus the only coordinate hypotheses are the
actual affine identities `d/e = s₀ S` and `v/u = s₀² T`; the required
row-scaled transport is proved internally. -/
theorem sourceOrientedSelectedIntegralMinor_det_eq_zero_of_reindexedSheared_abs_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (hsmall :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
            (shearedExponentialEvaluationMatrix A B S T)).det| < 1) :
    ((sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).submatrix r id).det =
      0 := by
  apply selectedIntegralMinor_det_eq_zero_of_reindexedShearedTransport_abs_lt_one
    A B (sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points)
    eRows r hr s₀ S T
    (fun row => ((points row).1.2 : ℝ) ^ A * ((points row).2.2 : ℝ) ^ B)
    hS hT
  · have hfull := sourceOrientedClearedEvaluationMatrix_map_eq_rowScale_centeredAffine
      A B points s₀ S T hden hcoords
    rw [hfull, submatrix_rowScale]
  · exact hsmall

/-- Vanishing of a source-oriented selected minor transfers to the standard
homogeneous selected minor by the explicit reflection of the two coefficient
indices. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_sourceOriented
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hzero :
      ((sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).submatrix r id).det =
        0) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  let reflection := generalBidegreeFormIndexReflection A B
  let standardMinor :=
    (generalBidegreeFormEvaluationMatrix A B points).submatrix r id
  have hminor_eq :
      (sourceOrientedGeneralBidegreeClearedEvaluationMatrix A B points).submatrix r id =
        standardMinor.submatrix (Equiv.refl _) reflection := by
    rw [sourceOrientedClearedEvaluationMatrix_eq_standard_columnReflection]
    ext i j
    rfl
  have hreflection_zero :
      (standardMinor.submatrix (Equiv.refl _) reflection).det = 0 := by
    rw [← hminor_eq]
    exact hzero
  have habs := Matrix.abs_det_submatrix_equiv_equiv
    (Equiv.refl (generalBidegreeFormIndex A B)) reflection standardMinor
  have hstandard_abs : |standardMinor.det| = 0 := by
    rw [hreflection_zero, abs_zero] at habs
    exact habs.symm
  exact abs_eq_zero.mp hstandard_abs

/-- The fully source-oriented-to-standard integral bridge.  Explicit local
coordinate and denominator hypotheses, together with a strict bound on the
reindexed sheared determinant after the displayed costs, force vanishing of
the corresponding standard integral selected minor. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_reindexedSheared_abs_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    (s₀ : ℝ) (S T : ι → ℝ)
    (hden : ∀ row, (points row).1.2 ≠ 0 ∧ (points row).2.2 ≠ 0)
    (hcoords : ∀ row,
      ((points row).1.1 : ℝ) / ((points row).1.2 : ℝ) = s₀ * S row ∧
        ((points row).2.1 : ℝ) / ((points row).2.2 : ℝ) = s₀ ^ 2 * T row)
    (hS : ∀ row, 0 < S row) (hT : ∀ row, 0 < T row)
    (hsmall :
      |(∏ i : generalBidegreeFormIndex A B,
          ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
          s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
            (shearedExponentialEvaluationMatrix A B S T)).det| < 1) :
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0 := by
  apply standardSelectedIntegralMinor_det_eq_zero_of_sourceOriented A B points r
  exact sourceOrientedSelectedIntegralMinor_det_eq_zero_of_reindexedSheared_abs_lt_one
    A B points eRows r hr s₀ S T hden hcoords hS hT hsmall

end PellPaper
