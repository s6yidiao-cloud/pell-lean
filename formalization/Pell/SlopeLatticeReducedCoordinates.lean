import Pell.SlopeLatticePrimitiveMinimum
import Pell.SL2RoundedColumn
import Pell.ReducedRealColumnBounds

/-!
# Actual reduced integer coordinates for the literal slope map

An attained primitive first-minimum column is completed in `SL(2, ℤ)` and
rounded in a dominant transformed coordinate. One resulting integer linear
equivalence works for every real radius and every integer vector. The widths
retain the determinant `M/(U*V)` and do not assert an integer-box count,
coefficient-height bound, or analytic square estimate.
-/

namespace PellPaper

open scoped MatrixGroups

/-- One literal real component of the slope map, as an additive functional
on integer vectors. No positivity is needed to define the map. -/
noncomputable def slopeCoordinateAddHom (U V M z : ℝ) (i : Fin 2) :
    (Fin 2 → ℤ) →+ ℝ where
  toFun v := ![M * (v 0 : ℝ) / V - z * (v 1 : ℝ) / U, (v 1 : ℝ) / U] i
  map_zero' := by fin_cases i <;> simp
  map_add' v w := by
    fin_cases i <;> simp <;> ring

/-- The component functionals give exactly the existing literal sup norm. -/
theorem slopeVectorSupNorm_eq_max_components (U V M z : ℝ) (v : Fin 2 → ℤ) :
    slopeVectorSupNorm U V M z (v 0, v 1) =
      max |slopeCoordinateAddHom U V M z 0 v| |slopeCoordinateAddHom U V M z 1 v| :=
  rfl

/-- An integer determinant-one change of columns retains the literal real
determinant. This algebraic identity also holds at zero denominators. -/
theorem slopeCoordinateAddHom_column_determinant (U V M z : ℝ) (W : SL(2, ℤ)) :
    slopeCoordinateAddHom U V M z 0 (fun i => W i 0) *
        slopeCoordinateAddHom U V M z 1 (fun i => W i 1) -
      slopeCoordinateAddHom U V M z 1 (fun i => W i 0) *
        slopeCoordinateAddHom U V M z 0 (fun i => W i 1) = M / (U * V) := by
  have hdetZ : W 0 0 * W 1 1 - W 0 1 * W 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using W.det_coe
  have hdetR : (W 0 0 : ℝ) * (W 1 1 : ℝ) -
      (W 0 1 : ℝ) * (W 1 0 : ℝ) = 1 := by exact_mod_cast hdetZ
  change (M * (W 0 0 : ℝ) / V - z * (W 1 0 : ℝ) / U) * ((W 1 1 : ℝ) / U) -
    ((W 1 0 : ℝ) / U) * (M * (W 0 1 : ℝ) / V - z * (W 1 1 : ℝ) / U) = _
  calc
    _ = M / (U * V) * ((W 0 0 : ℝ) * (W 1 1 : ℝ) -
        (W 0 1 : ℝ) * (W 1 0 : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = M / (U * V) := by rw [hdetR, mul_one]

/-- The installed integer linear equivalence recovers the literal slope
components as a linear combination of its transformed columns. -/
theorem slopeCoordinateAddHom_inverse_coordinates
    (U V M z : ℝ) (W : SL(2, ℤ)) (v : Fin 2 → ℤ) (i : Fin 2) :
    let x := W.toLin'.symm v
    slopeCoordinateAddHom U V M z i v =
      (x 0 : ℝ) * slopeCoordinateAddHom U V M z i (fun j => W j 0) +
        (x 1 : ℝ) * slopeCoordinateAddHom U V M z i (fun j => W j 1) := by
  let x := W.toLin'.symm v
  have hv : v = x 0 • (fun j => W j 0) + x 1 • (fun j => W j 1) := by
    rw [← W.toLin'.apply_symm_apply v]
    change W.toLin' x = _
    funext j
    change Matrix.mulVec W.1 x j = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  change slopeCoordinateAddHom U V M z i v = _
  calc
    _ = slopeCoordinateAddHom U V M z i
        (x 0 • (fun j => W j 0) + x 1 • (fun j => W j 1)) :=
      congrArg (slopeCoordinateAddHom U V M z i) hv
    _ = _ := by rw [map_add, map_zsmul, map_zsmul]; simp only [zsmul_eq_mul, x]

/-- One determinant-one integer coordinate system works for every radius
and vector in the literal slope-norm ball. Its first column attains the
actual first minimum; no reduction certificate is supplied by the caller. -/
theorem exists_SL2_reduced_slope_coordinates
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ W : SL(2, ℤ),
      slopeVectorSupNorm U V M z (W 0 0, W 1 0) = firstSlopeSupNorm U V M z ∧
      ∀ (R : ℝ) (v : Fin 2 → ℤ), slopeVectorSupNorm U V M z (v 0, v 1) ≤ R →
        let x := W.toLin'.symm v
        |(x 0 : ℝ)| ≤ 2 * R / firstSlopeSupNorm U V M z ∧
          |(x 1 : ℝ)| ≤ 2 * firstSlopeSupNorm U V M z * R / (M / (U * V)) := by
  let mu := firstSlopeSupNorm U V M z
  have hmu : 0 < mu := firstSlopeSupNorm_pos U V M z hU hV hM
  have hdelta : 0 < M / (U * V) := div_pos hM (mul_pos hU hV)
  have hsq : mu ^ 2 ≤ M / (U * V) := by
    have hupper := firstSlopeSupNorm_le_sqrt U V M z hU hV hM
    have hsqrt := Real.sq_sqrt hdelta.le
    change mu ≤ Real.sqrt (M / (U * V)) at hupper
    nlinarith [Real.sqrt_nonneg (M / (U * V))]
  obtain ⟨W0, hW0⟩ := exists_SL2_firstSlopeSupNorm U V M z hU hV hM
  have hmax : max |slopeCoordinateAddHom U V M z 0 (fun j => W0 j 0)|
      |slopeCoordinateAddHom U V M z 1 (fun j => W0 j 0)| = mu := hW0
  have hp0 : ∀ i : Fin 2, |slopeCoordinateAddHom U V M z i (fun j => W0 j 0)| ≤ mu := by
    intro i
    fin_cases i
    · exact (le_max_left _ _).trans hmax.le
    · exact (le_max_right _ _).trans hmax.le
  have hdom : ∃ i : Fin 2,
      |slopeCoordinateAddHom U V M z i (fun j => W0 j 0)| = mu := by
    rcases le_total |slopeCoordinateAddHom U V M z 0 (fun j => W0 j 0)|
        |slopeCoordinateAddHom U V M z 1 (fun j => W0 j 0)| with h | h
    · exact ⟨1, (max_eq_right h).symm.trans hmax⟩
    · exact ⟨0, (max_eq_left h).symm.trans hmax⟩
  obtain ⟨i, hi⟩ := hdom
  have hnonzero : slopeCoordinateAddHom U V M z i (fun j => W0 j 0) ≠ 0 := by
    intro hz
    have : mu = 0 := hi.symm.trans (by rw [hz, abs_zero])
    exact hmu.ne' this
  obtain ⟨W, _, hsame, _, hround⟩ :=
    exists_sl2_rounded_column W0 (slopeCoordinateAddHom U V M z i) hnonzero
  have hfirst : (W 0 0, W 1 0) = (W0 0 0, W0 1 0) :=
    Prod.ext (congrFun hsame 0) (congrFun hsame 1)
  refine ⟨W, by rw [hfirst]; exact hW0, ?_⟩
  intro R v hv
  let x := W.toLin'.symm v
  let p : Fin 2 → ℝ := fun j => slopeCoordinateAddHom U V M z j (fun k => W k 0)
  let q : Fin 2 → ℝ := fun j => slopeCoordinateAddHom U V M z j (fun k => W k 1)
  have hp : ∀ j, |p j| ≤ mu := by
    intro j
    change |slopeCoordinateAddHom U V M z j (fun k => W k 0)| ≤ mu
    rw [hsame]
    exact hp0 j
  have hdominant : ∃ j, |p j| = mu ∧ |q j| ≤ mu / 2 := by
    refine ⟨i, ?_, ?_⟩
    · change |slopeCoordinateAddHom U V M z i (fun k => W k 0)| = mu
      rw [hsame]
      exact hi
    · exact hround.trans_eq (congrArg (fun t : ℝ => t / 2) hi)
  have hdet : p 0 * q 1 - p 1 * q 0 = M / (U * V) :=
    slopeCoordinateAddHom_column_determinant U V M z W
  have hx : ∀ j, |(x 0 : ℝ) * p j + (x 1 : ℝ) * q j| ≤ R := by
    intro j
    have hid := slopeCoordinateAddHom_inverse_coordinates U V M z W v j
    change slopeCoordinateAddHom U V M z j v = (x 0 : ℝ) * p j + (x 1 : ℝ) * q j at hid
    rw [← hid]
    rw [slopeVectorSupNorm_eq_max_components] at hv
    fin_cases j
    · exact (le_max_left _ _).trans hv
    · exact (le_max_right _ _).trans hv
  exact abs_coordinates_le_of_reduced_columns p q (M / (U * V)) mu R
    (x 0 : ℝ) (x 1 : ℝ) hdelta hmu hdet hp hdominant hsq hx

/-- The two real halfwidths retain the exact thin-cell area scale. This
identity does not perform integer rounding or assert a finite count. -/
theorem slope_reduced_coordinate_halfwidth_product
    (U V M z R : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    (2 * R / firstSlopeSupNorm U V M z) *
        (2 * firstSlopeSupNorm U V M z * R / (M / (U * V))) =
      4 * R ^ 2 * U * V / M := by
  have hmu := firstSlopeSupNorm_pos U V M z hU hV hM
  field_simp [hmu.ne']
  ring

end PellPaper
