import Pell.ReducedDyadicTargetCover
import Pell.SlopeLatticeReciprocalMinimumSize
import Pell.DyadicTargetSlopeIntegerCover

/-!
# Explicit entry heights for the same reduced slope basis

The reduced-coordinate theorem already chooses one integral determinant-one
matrix before any radius or vector varies.  Here the two standard coordinate
vectors turn its universal inverse-coordinate estimates into bounds for all
four signed entries of that same matrix.  The reciprocal-minimum estimate
eliminates the minimum from the final matrix height.

No range hypothesis on the slope center is needed.  In particular, this is
not a choice of a second basis with unrelated height control.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- A common slope radius for the two standard integer coordinate vectors. -/
def slopeStandardBasisRadius (U V M z : ℝ) : ℝ :=
  max (M / V) (max |z| 1 / U)

/-- An explicit real height for every entry of the reduced slope matrix.
The inverse-coordinate estimates at the two standard basis vectors see all
four entries, and the center-independent reciprocal-minimum estimate removes
the actual first minimum from this bound. -/
def reducedSlopeMatrixEntryBound (U V M z : ℝ) : ℝ :=
  2 * slopeStandardBasisRadius U V M z * max U (V / M)

/-- The literal slope norms of both standard integer coordinate vectors are
bounded by the shared standard-basis radius. -/
theorem slopeVectorSupNorm_standardBasis_le
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (j : Fin 2) :
    slopeVectorSupNorm U V M z
        ((Pi.single j (1 : ℤ) : Fin 2 → ℤ) 0,
          (Pi.single j (1 : ℤ) : Fin 2 → ℤ) 1) ≤
      slopeStandardBasisRadius U V M z := by
  fin_cases j
  · change slopeVectorSupNorm U V M z (1, 0) ≤ slopeStandardBasisRadius U V M z
    have heq : slopeVectorSupNorm U V M z (1, 0) = M / V := by
      simp [slopeVectorSupNorm, abs_of_pos (div_pos hM hV)]
      positivity
    rw [heq]
    exact le_max_left _ _
  · change slopeVectorSupNorm U V M z (0, 1) ≤ slopeStandardBasisRadius U V M z
    have hz : |z / U| ≤ max |z| 1 / U := by
      rw [abs_div, abs_of_pos hU]
      exact div_le_div_of_nonneg_right (le_max_left _ _) hU.le
    rw [slopeVectorSupNorm]
    norm_num
    constructor
    · exact hz.trans (le_max_right _ _)
    · rw [slopeStandardBasisRadius, abs_of_pos hU]
      have hone' : U⁻¹ ≤ max |z| 1 / U := by
        rw [div_eq_mul_inv]
        simpa using mul_le_mul_of_nonneg_right (le_max_right |z| (1 : ℝ))
          (inv_nonneg.mpr hU.le)
      exact hone'.trans (le_max_right _ _)

/-- In dimension two, inverse images of the standard basis vectors are the
signed complementary columns.  This statement is kept local to the entry
height bridge rather than exposing a matrix-inverse representation choice. -/
theorem sl2_symm_standardBasis_apply
    (W : SL(2, ℤ)) (i j : Fin 2) :
    W.toLin'.symm (Pi.single j (1 : ℤ)) i = Matrix.adjugate W i j := by
  rw [Matrix.SpecialLinearGroup.toLin'_symm_apply, Matrix.toLin'_apply,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.mulVec_single_one]
  rfl

/-- One and the same reduced determinant-one basis has a fully explicit
entry height and the universal coordinate property.  The matrix is selected
before the radius and integer vector vary. -/
theorem exists_SL2_reduced_slope_coordinates_with_entry_bound
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ W : SL(2, ℤ),
      slopeVectorSupNorm U V M z (W 0 0, W 1 0) = firstSlopeSupNorm U V M z ∧
      (∀ i j, |((W i j : ℤ) : ℝ)| ≤ reducedSlopeMatrixEntryBound U V M z) ∧
      ∀ (R : ℝ) (v : Fin 2 → ℤ), slopeVectorSupNorm U V M z (v 0, v 1) ≤ R →
        let x := W.toLin'.symm v
        |(x 0 : ℝ)| ≤ 2 * R / firstSlopeSupNorm U V M z ∧
          |(x 1 : ℝ)| ≤ 2 * firstSlopeSupNorm U V M z * R / (M / (U * V)) := by
  obtain ⟨W, hfirst, hcoords⟩ :=
    exists_SL2_reduced_slope_coordinates U V M z hU hV hM
  let mu := firstSlopeSupNorm U V M z
  let delta := M / (U * V)
  let R0 := slopeStandardBasisRadius U V M z
  let C := max U (V / M)
  have hmu : 0 < mu := firstSlopeSupNorm_pos U V M z hU hV hM
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hsq : mu ^ 2 ≤ delta := by
    have hmule := firstSlopeSupNorm_le_sqrt U V M z hU hV hM
    have hsqrt := Real.sq_sqrt hdelta.le
    nlinarith [Real.sqrt_nonneg delta]
  have hC : reciprocalFirstSlopeSupNorm U V M z ≤ C := by
    exact reciprocalFirstSlopeSupNorm_le_max U V M z hU hV hM
  have hR0 : 0 ≤ R0 := by
    dsimp [R0, slopeStandardBasisRadius]
    positivity
  have hwide : 2 * mu * R0 / delta ≤ 2 * R0 / mu := by
    apply (div_le_div_iff₀ hdelta hmu).mpr
    calc
      2 * mu * R0 * mu = (2 * R0) * mu ^ 2 := by ring
      _ ≤ (2 * R0) * delta := by gcongr
      _ = 2 * R0 * delta := by ring
  have hrecip : 2 * R0 / mu ≤ 2 * R0 * C := by
    calc
      2 * R0 / mu = 2 * R0 * reciprocalFirstSlopeSupNorm U V M z := by
        simp only [reciprocalFirstSlopeSupNorm, mu]
        ring
      _ ≤ 2 * R0 * C := by gcongr
  have haxis0 := hcoords R0 (Pi.single 0 (1 : ℤ))
    (slopeVectorSupNorm_standardBasis_le U V M z hU hV hM 0)
  have haxis1 := hcoords R0 (Pi.single 1 (1 : ℤ))
    (slopeVectorSupNorm_standardBasis_le U V M z hU hV hM 1)
  have hinv00 : W.toLin'.symm (Pi.single 0 (1 : ℤ)) 0 = W 1 1 := by
    simpa [Matrix.adjugate_fin_two] using sl2_symm_standardBasis_apply W 0 0
  have hinv10 : W.toLin'.symm (Pi.single 0 (1 : ℤ)) 1 = -W 1 0 := by
    simpa [Matrix.adjugate_fin_two] using sl2_symm_standardBasis_apply W 1 0
  have hinv01 : W.toLin'.symm (Pi.single 1 (1 : ℤ)) 0 = -W 0 1 := by
    simpa [Matrix.adjugate_fin_two] using sl2_symm_standardBasis_apply W 0 1
  have hinv11 : W.toLin'.symm (Pi.single 1 (1 : ℤ)) 1 = W 0 0 := by
    simpa [Matrix.adjugate_fin_two] using sl2_symm_standardBasis_apply W 1 1
  refine ⟨W, hfirst, ?_, hcoords⟩
  intro i j
  fin_cases i <;> fin_cases j
  · have hx := haxis1.2.trans (hwide.trans hrecip)
    rw [hinv11] at hx
    change |((W 0 0 : ℤ) : ℝ)| ≤ reducedSlopeMatrixEntryBound U V M z
    simpa only [reducedSlopeMatrixEntryBound, R0, C] using hx
  · have hx := haxis1.1.trans hrecip
    rw [hinv01] at hx
    change |((W 0 1 : ℤ) : ℝ)| ≤ reducedSlopeMatrixEntryBound U V M z
    simpa only [Int.cast_neg, abs_neg, reducedSlopeMatrixEntryBound, R0, C] using hx
  · have hx := haxis0.2.trans (hwide.trans hrecip)
    rw [hinv10] at hx
    change |((W 1 0 : ℤ) : ℝ)| ≤ reducedSlopeMatrixEntryBound U V M z
    simpa only [Int.cast_neg, abs_neg, reducedSlopeMatrixEntryBound, R0, C] using hx
  · have hx := haxis0.1.trans hrecip
    rw [hinv00] at hx
    change |((W 1 1 : ℤ) : ℝ)| ≤ reducedSlopeMatrixEntryBound U V M z
    simpa only [reducedSlopeMatrixEntryBound, R0, C] using hx

/-- On the positive target-center range, and for coordinate scales at least
one, the generic entry height has a simple polynomial majorant. -/
theorem reducedSlopeMatrixEntryBound_le_six_mul
    (U V M z : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hM : 1 ≤ M)
    (hzlo : M / 2 ≤ z) (hzhi : z ≤ 3 * M) :
    reducedSlopeMatrixEntryBound U V M z ≤ 6 * M * (U + V) := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hznonneg : 0 ≤ z := (div_nonneg hMpos.le (by norm_num)).trans hzlo
  have hzabs : |z| = z := abs_of_nonneg hznonneg
  have hthreeM : 1 ≤ 3 * M := hM.trans (by nlinarith)
  have hzmax : max |z| 1 ≤ 3 * M := by
    rw [hzabs]
    exact max_le hzhi hthreeM
  have hMV : M / V ≤ M := div_le_self hMpos.le hV
  have hzU : max |z| 1 / U ≤ 3 * M := by
    exact (div_le_self (by positivity : 0 ≤ max |z| 1) hU).trans hzmax
  have hR : slopeStandardBasisRadius U V M z ≤ 3 * M :=
    max_le (hMV.trans (by nlinarith)) hzU
  have hVM : V / M ≤ V := div_le_self hVpos.le hM
  have hC : max U (V / M) ≤ U + V := max_le (by linarith) (hVM.trans (by linarith))
  rw [reducedSlopeMatrixEntryBound]
  calc
    2 * slopeStandardBasisRadius U V M z * max U (V / M) ≤
        2 * (3 * M) * (U + V) := by gcongr
    _ = 6 * M * (U + V) := by ring

/-- For an actual dyadic target center, the same reduced matrix simultaneously
has the polynomial entry bound and covers every later literal target image.
The matrix is selected after `i,M,k` but before `theta,Y,j`; no second basis
is introduced. -/
theorem exists_reduced_dyadicSourceTargetImage_cover_with_entry_bound
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (k : ℤ) (hM : 0 < M)
    (hk : k ∈ targetSlopeIntegerCenters (M : ℝ)) :
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
    let delta := (M : ℝ) / (U * V)
    let A := 4 / mu
    let B := 4 * mu / delta
    ∃ W : SL(2, ℤ),
      slopeVectorSupNorm U V (M : ℝ) (k : ℝ) (W 0 0, W 1 0) = mu ∧
      (∀ a b, |((W a b : ℤ) : ℝ)| ≤ 6 * (M : ℝ) * (U + V)) ∧
      (∀ (R : ℝ) (v : Fin 2 → ℤ),
        slopeVectorSupNorm U V (M : ℝ) (k : ℝ) (v 0, v 1) ≤ R →
          let x := W.toLin'.symm v
          |(x 0 : ℝ)| ≤ 2 * R / mu ∧ |(x 1 : ℝ)| ≤ 2 * mu * R / delta) ∧
      ∀ (theta : ℝ) (Y j : ℕ),
        let T := dyadicSourceTargetImage theta Y i M j k
        let C := sl2InverseTargetImage W T
        C.card = T.card ∧
        (∀ x ∈ C, IsCoprime (x 0) (x 1)) ∧
        (∀ y ∈ T, W.toLin' (W.toLin'.symm y) = y) ∧
        C ⊆ integerSymmetricRectangle A B ∧
        (T.Nonempty → 2 ≤ A) ∧
        (B < 1 → T.card ≤ 2) ∧
        (T.Nonempty → 1 ≤ B →
          ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / (M : ℝ) ∧
          ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
          ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta ∧
          ((integerSymmetricInterval A).card : ℝ) +
            ((integerSymmetricInterval B).card : ℝ) ≤ 24 / mu) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
  let delta := (M : ℝ) / (U * V)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hUone : 1 ≤ U := by dsimp [U]; exact_mod_cast Nat.one_le_two_pow
  have hVone : 1 ≤ V := by dsimp [V]; exact_mod_cast Nat.one_le_two_pow
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨hklo, hkhi⟩ := targetSlopeIntegerCenters_range (M : ℝ) hk
  obtain ⟨W, hfirst, hentry, hcoords⟩ :=
    exists_SL2_reduced_slope_coordinates_with_entry_bound
      U V (M : ℝ) (k : ℝ) hU hV hMr
  have hentry' : ∀ a b, |((W a b : ℤ) : ℝ)| ≤ 6 * (M : ℝ) * (U + V) := by
    intro a b
    exact (hentry a b).trans
      (reducedSlopeMatrixEntryBound_le_six_mul U V (M : ℝ) (k : ℝ)
        hUone hVone hMone hklo hkhi)
  refine ⟨W, hfirst, hentry', hcoords, ?_⟩
  intro theta Y j
  let T := dyadicSourceTargetImage theta Y i M j k
  have hp : ∀ y ∈ T, IsCoprime (y 0) (y 1) :=
    fun _ hy => (dyadicSourceTargetImage_primitive_and_supNorm hy).1
  have hw : ∀ y ∈ T, |(W.toLin'.symm y 0 : ℝ)| ≤ 4 / mu ∧
      |(W.toLin'.symm y 1 : ℝ)| ≤ 4 * mu / delta := by
    intro y hy
    have h := hcoords 2 y (dyadicSourceTargetImage_primitive_and_supNorm hy).2
    dsimp [mu, delta]
    constructor
    · convert h.1 using 1
      all_goals ring
    · convert h.2 using 1
      all_goals ring
  refine ⟨card_sl2InverseTargetImage W T,
    primitive_sl2InverseTargetImage W T hp,
    fun y _ => W.toLin'.apply_symm_apply y, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_integerSymmetricRectangle _ _ _).mpr (hw y hy)
  · intro hT
    have hs : mu ≤ 2 := firstSlopeSupNorm_le_two_of_dyadicSourceTargetImage_nonempty hM hT
    have hmu : 0 < mu := firstSlopeSupNorm_pos U V (M : ℝ) (k : ℝ) hU hV hMr
    exact (le_div_iff₀ hmu).mpr (by linarith)
  · exact card_targets_le_two_of_sl2_inverse_thin W T (4 * mu / delta) hp
      (fun y hy => (hw y hy).2)
  · intro hT hB
    have hs : mu ≤ 2 := firstSlopeSupNorm_le_two_of_dyadicSourceTargetImage_nonempty hM hT
    exact (slope_reduced_integer_rectangle_budgets U V (M : ℝ) (k : ℝ)
      hU hV hMr hs hB).2

end

end PellPaper
