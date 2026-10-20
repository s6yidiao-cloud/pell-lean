import Pell.Main3LargeAnalyticFixedKeyCellTargetCompletionEntryBoundCover
import Mathlib.Tactic

/-!
# Coarse height bounds for a bounded primitive completion

The primitive-wedge target cover now retains the same bounded completion
matrix `G` that is used to define the slope centre.  This file records the
elementary height estimates needed downstream: an additive functional on a
column of `G`, the induced slope centre, and a centre-independent coarse
majorant for the reduced slope matrix.

The statements are parameter-free.  Main3 branch adapters remain responsible
for supplying bounds on the additive functional at the two standard vectors.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- An additive real functional evaluated on one column of a bounded integral
matrix is bounded by twice the entry height times its standard-basis height. -/
theorem abs_addHom_sl2_column_le
    (ell : (Fin 2 → ℤ) →+ ℝ) (G : SL(2, ℤ)) (T Q : ℝ)
    (hT : 0 ≤ T)
    (hentry : ∀ i j, |((G i j : ℤ) : ℝ)| ≤ T)
    (hell : ∀ i, |ell (Pi.single i (1 : ℤ))| ≤ Q)
    (j : Fin 2) :
    |ell (fun i ↦ G i j)| ≤ 2 * T * Q := by
  have hcolumn : (fun i ↦ G i j) =
      G 0 j • (Pi.single 0 (1 : ℤ) : Fin 2 → ℤ) +
        G 1 j • (Pi.single 1 (1 : ℤ) : Fin 2 → ℤ) := by
    funext i
    fin_cases i <;> simp
  rw [hcolumn, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]
  calc
    |(G 0 j : ℝ) * ell (Pi.single 0 (1 : ℤ)) +
          (G 1 j : ℝ) * ell (Pi.single 1 (1 : ℤ))| ≤
        |(G 0 j : ℝ) * ell (Pi.single 0 (1 : ℤ))| +
          |(G 1 j : ℝ) * ell (Pi.single 1 (1 : ℤ))| := abs_add_le _ _
    _ = |((G 0 j : ℤ) : ℝ)| * |ell (Pi.single 0 (1 : ℤ))| +
          |((G 1 j : ℤ) : ℝ)| * |ell (Pi.single 1 (1 : ℤ))| := by
      rw [abs_mul, abs_mul]
    _ ≤ T * Q + T * Q := by
      exact add_le_add
        (mul_le_mul (hentry 0 j) (hell 0) (abs_nonneg _) hT)
        (mul_le_mul (hentry 1 j) (hell 1) (abs_nonneg _) hT)
    _ = 2 * T * Q := by ring

/-- The slope centre `-K*beta/R` inherits the column-functional height. -/
theorem abs_neg_mul_addHom_sl2_column_div_le
    (ell : (Fin 2 → ℤ) →+ ℝ) (G : SL(2, ℤ))
    (T Q K R : ℝ)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hR : 0 < R)
    (hentry : ∀ i j, |((G i j : ℤ) : ℝ)| ≤ T)
    (hell : ∀ i, |ell (Pi.single i (1 : ℤ))| ≤ Q)
    (j : Fin 2) :
    |-K * ell (fun i ↦ G i j) / R| ≤ 2 * K * T * Q / R := by
  have hbeta := abs_addHom_sl2_column_le ell G T Q hT hentry hell j
  rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hK, abs_of_pos hR]
  apply (div_le_div_iff_of_pos_right hR).2
  calc
    K * |ell (fun i ↦ G i j)| ≤ K * (2 * T * Q) := by gcongr
    _ = 2 * K * T * Q := by ring

/-- With no sign restriction on the centre, the two maxima in the reduced
matrix height are bounded by the corresponding positive sums.  This is the
form used when `U = K/2` may be smaller than one. -/
theorem reducedSlopeMatrixEntryBound_le_expanded
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    reducedSlopeMatrixEntryBound U V M z ≤
      2 * (M / V + |z| / U + 1 / U) * (U + V / M) := by
  have hMV : 0 ≤ M / V := div_nonneg hM.le hV.le
  have hzU : 0 ≤ |z| / U := div_nonneg (abs_nonneg z) hU.le
  have honeU : 0 ≤ 1 / U := by positivity
  have hmaxz : max |z| 1 / U ≤ |z| / U + 1 / U := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right
      (max_le (le_add_of_nonneg_right (by norm_num))
        (le_add_of_nonneg_left (abs_nonneg z))) hU.le
  have hR : slopeStandardBasisRadius U V M z ≤
      M / V + |z| / U + 1 / U := by
    unfold slopeStandardBasisRadius
    apply max_le
    · linarith
    · linarith
  have hC : max U (V / M) ≤ U + V / M := by
    exact max_le (le_add_of_nonneg_right (div_nonneg hV.le hM.le))
      (le_add_of_nonneg_left hU.le)
  have hRnonneg : 0 ≤ slopeStandardBasisRadius U V M z := by
    unfold slopeStandardBasisRadius
    exact hMV.trans (le_max_left _ _)
  rw [reducedSlopeMatrixEntryBound]
  gcongr

/-- If all three positive slope scales are at least one, separate upper
bounds for the scales and the centre further give a polynomial majorant. -/
theorem reducedSlopeMatrixEntryBound_le_coarse
    (U V M z Ubar Vbar Mbar Zbar : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hM : 1 ≤ M)
    (hUbar : U ≤ Ubar) (hVbar : V ≤ Vbar)
    (hMbar : M ≤ Mbar) (hz : |z| ≤ Zbar) (hZbar : 1 ≤ Zbar) :
    reducedSlopeMatrixEntryBound U V M z ≤
      2 * (Mbar + Zbar) * (Ubar + Vbar) := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMbarNonneg : 0 ≤ Mbar := by linarith
  have hZbarNonneg : 0 ≤ Zbar := by linarith
  have hUbarNonneg : 0 ≤ Ubar := by linarith
  have hVbarNonneg : 0 ≤ Vbar := by linarith
  have hMV : M / V ≤ Mbar + Zbar := by
    calc
      M / V ≤ M := div_le_self hMpos.le hV
      _ ≤ Mbar := hMbar
      _ ≤ Mbar + Zbar := le_add_of_nonneg_right hZbarNonneg
  have hzU : max |z| 1 / U ≤ Mbar + Zbar := by
    calc
      max |z| 1 / U ≤ max |z| 1 :=
        div_le_self ((abs_nonneg z).trans (le_max_left _ _)) hU
      _ ≤ Zbar := max_le hz hZbar
      _ ≤ Mbar + Zbar := le_add_of_nonneg_left hMbarNonneg
  have hR : slopeStandardBasisRadius U V M z ≤ Mbar + Zbar :=
    max_le hMV hzU
  have hVM : V / M ≤ Ubar + Vbar := by
    calc
      V / M ≤ V := div_le_self hVpos.le hM
      _ ≤ Vbar := hVbar
      _ ≤ Ubar + Vbar := le_add_of_nonneg_left hUbarNonneg
  have hC : max U (V / M) ≤ Ubar + Vbar :=
    max_le (hUbar.trans (le_add_of_nonneg_right hVbarNonneg)) hVM
  have hRnonneg : 0 ≤ slopeStandardBasisRadius U V M z := by
    unfold slopeStandardBasisRadius
    positivity
  rw [reducedSlopeMatrixEntryBound]
  gcongr

/-- The product-basis entry bound used by the primitive-wedge cover inherits
the expanded reduced-matrix estimate. -/
theorem primitiveWedgeProductEntryHeight_le_expanded
    (T₀ U V M z : ℝ) (hT₀ : 0 ≤ T₀)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M z ≤
      4 * (T₀ + 1) * (M / V + |z| / U + 1 / U) *
        (U + V / M) := by
  have hT₀one : 0 ≤ T₀ + 1 := by linarith
  have hbound := reducedSlopeMatrixEntryBound_le_expanded U V M z hU hV hM
  calc
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M z ≤
        2 * (T₀ + 1) *
          (2 * (M / V + |z| / U + 1 / U) * (U + V / M)) := by
      gcongr
    _ = 4 * (T₀ + 1) * (M / V + |z| / U + 1 / U) *
          (U + V / M) := by ring

/-- Under unit lower bounds, the product-basis height also inherits the
coarser bar-parameter estimate. -/
theorem primitiveWedgeProductEntryHeight_le_coarse
    (T₀ U V M z Ubar Vbar Mbar Zbar : ℝ)
    (hT₀ : 0 ≤ T₀)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hM : 1 ≤ M)
    (hUbar : U ≤ Ubar) (hVbar : V ≤ Vbar)
    (hMbar : M ≤ Mbar) (hz : |z| ≤ Zbar) (hZbar : 1 ≤ Zbar) :
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M z ≤
      4 * (T₀ + 1) * (Mbar + Zbar) * (Ubar + Vbar) := by
  have hT₀one : 0 ≤ T₀ + 1 := by linarith
  have hbound := reducedSlopeMatrixEntryBound_le_coarse
    U V M z Ubar Vbar Mbar Zbar hU hV hM
      hUbar hVbar hMbar hz hZbar
  calc
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M z ≤
        2 * (T₀ + 1) * (2 * (Mbar + Zbar) * (Ubar + Vbar)) := by
      gcongr
    _ = 4 * (T₀ + 1) * (Mbar + Zbar) * (Ubar + Vbar) := by ring

end

end PellPaper
