import Pell.BinaryProjectiveDerivativeResultant
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic

/-!
# An affine squarefreeness certificate for the projective derivative resultant

This extracts the resultant calculation from
`BinaryProjectiveDerivativeResultantSquarefree`. Its input is rational
squarefreeness on the chart (X,1) and a degree gap of at most one: the latter
allows a single factor at infinity but excludes a repeated one. No
multivariate or algebraic-closure squarefreeness hypothesis is imposed.

The local identities below are copied from the reviewed calculation because
they are private in the existing module. The fixed bounds j-1,j-1 of the
actual integral resultant are preserved, including the degree-one case.
-/

namespace PellPaper

open Polynomial

noncomputable section

private theorem natDegree_binaryDehomogenizeAtOne_le_totalDegree'
    {R : Type*} [CommRing R] [Nontrivial R] (J : MvPolynomial (Fin 2) R) :
    (binaryDehomogenizeAtOne J).natDegree ≤ J.totalDegree := by
  rw [binaryDehomogenizeAtOne, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two, one_pow, mul_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact (Finsupp.le_degree 0 d).trans (MvPolynomial.le_totalDegree hd)

private theorem coeff_euler_companion_at_natDegree
    {K : Type*} [Field K] [CharZero K] (P : K[X]) (j : ℕ)
    (hj : j = P.natDegree + 1) :
    (Polynomial.C (j : K) * P - Polynomial.X * P.derivative).coeff P.natDegree =
      P.leadingCoeff := by
  cases hdeg : P.natDegree with
  | zero =>
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul_zero, ← hdeg, Polynomial.coeff_natDegree]
      simp [hj, hdeg]
  | succ m =>
      have hcoeff : P.coeff (m + 1) = P.leadingCoeff := by
        rw [← hdeg, Polynomial.coeff_natDegree]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      rw [hcoeff]
      push_cast [hj, hdeg]
      ring

private theorem binaryDehomogenizeAtOne_pderiv_zero'
    {R : Type*} [CommSemiring R] (J : MvPolynomial (Fin 2) R) :
    binaryDehomogenizeAtOne (MvPolynomial.pderiv 0 J) =
      (binaryDehomogenizeAtOne J).derivative := by
  classical
  induction J using MvPolynomial.induction_on with
  | C a => simp [binaryDehomogenizeAtOne]
  | add p q hp hq =>
      have hp' :
          MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, (1 : Polynomial R)]
              (MvPolynomial.pderiv 0 p) =
            (MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, (1 : Polynomial R)] p).derivative := by
        simpa only [binaryDehomogenizeAtOne,
          MvPolynomial.coe_eval₂Hom] using hp
      have hq' :
          MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, (1 : Polynomial R)]
              (MvPolynomial.pderiv 0 q) =
            (MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, (1 : Polynomial R)] q).derivative := by
        simpa only [binaryDehomogenizeAtOne,
          MvPolynomial.coe_eval₂Hom] using hq
      rw [(MvPolynomial.pderiv 0).map_add]
      change MvPolynomial.eval₂ Polynomial.C
          ![Polynomial.X, (1 : Polynomial R)]
          (MvPolynomial.pderiv 0 p + MvPolynomial.pderiv 0 q) =
        (MvPolynomial.eval₂ Polynomial.C
          ![Polynomial.X, (1 : Polynomial R)] (p + q)).derivative
      rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add,
        Polynomial.derivative_add, hp', hq']
  | mul_X p i hp =>
      have hp' :
          MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, (1 : Polynomial R)]
              (MvPolynomial.pderiv 0 p) =
            (MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, (1 : Polynomial R)] p).derivative := by
        simpa only [binaryDehomogenizeAtOne,
          MvPolynomial.coe_eval₂Hom] using hp
      fin_cases i
      · simp [binaryDehomogenizeAtOne, MvPolynomial.pderiv_X,
          Polynomial.derivative_mul, mul_comm]
        rw [hp']
      · simp [binaryDehomogenizeAtOne, MvPolynomial.pderiv_X]
        exact hp'

private theorem binaryDehomogenizeAtOne_pderiv_one_of_isHomogeneous'
    {R : Type*} [CommRing R] (J : MvPolynomial (Fin 2) R) (j : ℕ)
    (hJ : J.IsHomogeneous j) :
    binaryDehomogenizeAtOne (MvPolynomial.pderiv 1 J) =
      Polynomial.C (j : R) * binaryDehomogenizeAtOne J -
        Polynomial.X * (binaryDehomogenizeAtOne J).derivative := by
  have hEuler :
      MvPolynomial.X 0 * MvPolynomial.pderiv 0 J +
          MvPolynomial.X 1 * MvPolynomial.pderiv 1 J = j • J := by
    simpa [Fin.sum_univ_two] using hJ.sum_X_mul_pderiv
  have h := congrArg (fun Q : MvPolynomial (Fin 2) R ↦
      binaryDehomogenizeAtOne Q) hEuler
  change MvPolynomial.eval₂Hom Polynomial.C
      ![Polynomial.X, (1 : Polynomial R)]
        (MvPolynomial.X 0 * MvPolynomial.pderiv 0 J +
          MvPolynomial.X 1 * MvPolynomial.pderiv 1 J) =
    MvPolynomial.eval₂Hom Polynomial.C
      ![Polynomial.X, (1 : Polynomial R)] (j • J) at h
  simp only [map_add, map_mul, map_nsmul, MvPolynomial.eval₂Hom_X'] at h
  simp at h
  have hzero :
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, (1 : Polynomial R)]
          (MvPolynomial.pderiv 0 J) =
        (MvPolynomial.eval₂ Polynomial.C
          ![Polynomial.X, (1 : Polynomial R)] J).derivative := by
    simpa only [binaryDehomogenizeAtOne,
      MvPolynomial.coe_eval₂Hom] using
        binaryDehomogenizeAtOne_pderiv_zero' J
  rw [hzero] at h
  change MvPolynomial.eval₂ Polynomial.C
      ![Polynomial.X, (1 : Polynomial R)] (MvPolynomial.pderiv 1 J) =
    Polynomial.C (j : R) *
      MvPolynomial.eval₂ Polynomial.C
        ![Polynomial.X, (1 : Polynomial R)] J -
      Polynomial.X *
        (MvPolynomial.eval₂ Polynomial.C
          ![Polynomial.X, (1 : Polynomial R)] J).derivative
  rw [eq_sub_iff_add_eq]
  simpa [nsmul_eq_mul, Polynomial.C_eq_natCast, add_comm] using h

private theorem binaryProjectiveDerivativeResultant_ne_zero_of_affine_squarefree_field
    {K : Type*} [Field K] [CharZero K]
    (H : MvPolynomial (Fin 2) K) (j : ℕ)
    (hH : H.IsHomogeneous j) (hj : 0 < j)
    (hsq : Squarefree (binaryDehomogenizeAtOne H))
    (hgap : j ≤ (binaryDehomogenizeAtOne H).natDegree + 1) :
    binaryProjectiveDerivativeResultant H j ≠ 0 := by
  let P : K[X] := binaryDehomogenizeAtOne H
  let A : K[X] := binaryDehomogenizeAtOne (MvPolynomial.pderiv 0 H)
  let B : K[X] := binaryDehomogenizeAtOne (MvPolynomial.pderiv 1 H)
  have hPdeg : P.natDegree ≤ j :=
    (natDegree_binaryDehomogenizeAtOne_le_totalDegree' H).trans hH.totalDegree_le
  have hPdegLower : j ≤ P.natDegree + 1 :=
    hgap
  have hPcases : P.natDegree = j ∨ P.natDegree = j - 1 := by omega
  have hAformula : A = P.derivative :=
    binaryDehomogenizeAtOne_pderiv_zero' H
  have hBformula :
      B = Polynomial.C (j : K) * P - Polynomial.X * P.derivative :=
    binaryDehomogenizeAtOne_pderiv_one_of_isHomogeneous' H j hH
  have hAhom : (MvPolynomial.pderiv 0 H).IsHomogeneous (j - 1) := hH.pderiv
  have hBhom : (MvPolynomial.pderiv 1 H).IsHomogeneous (j - 1) := hH.pderiv
  have hAdeg : A.natDegree ≤ j - 1 :=
    (natDegree_binaryDehomogenizeAtOne_le_totalDegree' _).trans hAhom.totalDegree_le
  have hBdeg : B.natDegree ≤ j - 1 :=
    (natDegree_binaryDehomogenizeAtOne_le_totalDegree' _).trans hBhom.totalDegree_le
  have hsqP : Squarefree P :=
    hsq
  have hcopPP : IsCoprime P P.derivative :=
    (Polynomial.separable_def P).mp
      (PerfectField.separable_iff_squarefree.mpr hsqP)
  have hjK : (j : K) ≠ 0 := by exact_mod_cast hj.ne'
  have hcopAB : IsCoprime A B := by
    rcases hcopPP with ⟨u, v, huv⟩
    refine ⟨v + u * Polynomial.C (j : K)⁻¹ * Polynomial.X,
      u * Polynomial.C (j : K)⁻¹, ?_⟩
    rw [hAformula, hBformula]
    calc
      (v + u * Polynomial.C (j : K)⁻¹ * Polynomial.X) * P.derivative +
          (u * Polynomial.C (j : K)⁻¹) *
            (Polynomial.C (j : K) * P - Polynomial.X * P.derivative) =
        u * (Polynomial.C (j : K)⁻¹ * Polynomial.C (j : K)) * P +
          v * P.derivative := by ring
      _ = u * P + v * P.derivative := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hjK, map_one, mul_one]
      _ = 1 := huv
  have hresStandard : Polynomial.resultant A B ≠ 0 :=
    Polynomial.resultant_ne_zero A B hcopAB
  change Polynomial.resultant A B (j - 1) (j - 1) ≠ 0
  rcases hPcases with hPj | hPj
  · have hAeq : A.natDegree = j - 1 := by
      rw [hAformula, Polynomial.natDegree_derivative, hPj]
    have hA0 : A ≠ 0 := by
      rw [hAformula, Polynomial.derivative_ne_zero]
      omega
    have hAcoeff : A.coeff (j - 1) ≠ 0 := by
      rw [← hAeq, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hA0
    have hpad := Polynomial.resultant_add_right_deg
      A B (j - 1) B.natDegree (j - 1 - B.natDegree) le_rfl
    have hsum : B.natDegree + (j - 1 - B.natDegree) = j - 1 :=
      Nat.add_sub_of_le hBdeg
    rw [hsum] at hpad
    have hresStandard' :
        Polynomial.resultant A B (j - 1) B.natDegree ≠ 0 := by
      simpa only [hAeq] using hresStandard
    rw [hpad]
    exact mul_ne_zero (pow_ne_zero _ hAcoeff) hresStandard'
  · have hjSucc : j = P.natDegree + 1 := by omega
    have hBcoeff : B.coeff (j - 1) ≠ 0 := by
      rw [hBformula]
      have heq := coeff_euler_companion_at_natDegree P j hjSucc
      rw [show j - 1 = P.natDegree by omega, heq]
      exact Polynomial.leadingCoeff_ne_zero.mpr hsqP.ne_zero
    have hBeq : B.natDegree = j - 1 := by
      apply Nat.le_antisymm hBdeg
      by_contra hlt
      exact hBcoeff (Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hlt))
    have hpad := Polynomial.resultant_add_left_deg
      A B A.natDegree (j - 1) (j - 1 - A.natDegree) le_rfl
    have hsum : A.natDegree + (j - 1 - A.natDegree) = j - 1 :=
      Nat.add_sub_of_le hAdeg
    rw [hsum] at hpad
    have hresStandard' :
        Polynomial.resultant A B A.natDegree (j - 1) ≠ 0 := by
      simpa only [hBeq] using hresStandard
    rw [hpad]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ hBcoeff)) hresStandard'

private theorem binaryDehomogenizeAtOne_map'
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : MvPolynomial (Fin 2) R) :
    binaryDehomogenizeAtOne (J.map f) =
      (binaryDehomogenizeAtOne J).map f := by
  rw [binaryDehomogenizeAtOne, MvPolynomial.eval₂Hom_map_hom]
  rw [binaryDehomogenizeAtOne]
  change _ = (Polynomial.mapRingHom f)
    (MvPolynomial.eval₂Hom Polynomial.C
      ![Polynomial.X, (1 : Polynomial R)] J)
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    simp
  · funext i
    fin_cases i <;> simp
  · rfl

private theorem binaryProjectiveDerivativeResultant_map'
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : MvPolynomial (Fin 2) R) (j : ℕ) :
    binaryProjectiveDerivativeResultant (J.map f) j =
      f (binaryProjectiveDerivativeResultant J j) := by
  have hzero : MvPolynomial.pderiv 0 (J.map f) =
      (MvPolynomial.pderiv 0 J).map f := MvPolynomial.pderiv_map
  have hone : MvPolynomial.pderiv 1 (J.map f) =
      (MvPolynomial.pderiv 1 J).map f := MvPolynomial.pderiv_map
  unfold binaryProjectiveDerivativeResultant
  rw [hzero, hone, binaryDehomogenizeAtOne_map',
    binaryDehomogenizeAtOne_map', Polynomial.resultant_map_map]

/-- Rational affine squarefreeness and at most a simple factor at infinity
give a nonzero integral projective derivative resultant. -/
theorem binaryProjectiveDerivativeResultant_ne_zero_of_affine_squarefree
    (J : MvPolynomial (Fin 2) ℤ) (j : ℕ)
    (hJ : J.IsHomogeneous j) (hj : 0 < j)
    (hsq : Squarefree ((binaryDehomogenizeAtOne J).map (Int.castRingHom ℚ)))
    (hgap : j ≤ (binaryDehomogenizeAtOne J).natDegree + 1) :
    binaryProjectiveDerivativeResultant J j ≠ 0 := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  let H : MvPolynomial (Fin 2) ℚ := J.map f
  have hsqH : Squarefree (binaryDehomogenizeAtOne H) := by
    change Squarefree (binaryDehomogenizeAtOne (J.map f))
    rw [binaryDehomogenizeAtOne_map']
    exact hsq
  have hgapH : j ≤ (binaryDehomogenizeAtOne H).natDegree + 1 := by
    change j ≤ (binaryDehomogenizeAtOne (J.map f)).natDegree + 1
    rw [binaryDehomogenizeAtOne_map', Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective f from Int.cast_injective)]
    exact hgap
  have hres : binaryProjectiveDerivativeResultant H j ≠ 0 :=
    binaryProjectiveDerivativeResultant_ne_zero_of_affine_squarefree_field
      H j (hJ.map f) hj hsqH hgapH
  rw [binaryProjectiveDerivativeResultant_map'] at hres
  exact fun hzero ↦ hres (by simp [hzero])

end
end PellPaper
