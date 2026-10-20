import Pell.SquarefreePolynomialLinearNonsquare
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

/-!
# A projective derivative resultant certificate for good binary reduction

For a homogeneous binary form `J` of degree `j`, this file packages the
fixed-bound resultant of the two dehomogenized partial derivatives.  If a
prime does not divide that integral resultant, reduction modulo the prime
has squarefree dehomogenization and retains affine degree at least `j - 1`.

The fixed bounds `j - 1, j - 1` are part of the definition.  In particular,
the certificate commutes with coefficient reduction even when leading
coefficients vanish modulo the prime.
-/

namespace PellPaper

open Polynomial

noncomputable section

private theorem binaryDehomogenizeAtOne_map
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

private theorem binaryDehomogenizeAtOne_pderiv_zero
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

private theorem binaryDehomogenizeAtOne_pderiv_one_of_isHomogeneous
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
        binaryDehomogenizeAtOne_pderiv_zero J
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

private theorem natDegree_binaryDehomogenizeAtOne_le_totalDegree
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

/-- The fixed-bound resultant of the two affine partial derivatives of a
binary form.  The supplied `j` records the intended homogeneous degree. -/
noncomputable def binaryProjectiveDerivativeResultant
    {R : Type*} [CommRing R] (J : MvPolynomial (Fin 2) R) (j : ℕ) : R :=
  Polynomial.resultant
    (binaryDehomogenizeAtOne (MvPolynomial.pderiv 0 J))
    (binaryDehomogenizeAtOne (MvPolynomial.pderiv 1 J))
    (j - 1) (j - 1)

private theorem binaryProjectiveDerivativeResultant_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : MvPolynomial (Fin 2) R) (j : ℕ) :
    binaryProjectiveDerivativeResultant (J.map f) j =
      f (binaryProjectiveDerivativeResultant J j) := by
  have hzero : MvPolynomial.pderiv 0 (J.map f) =
      (MvPolynomial.pderiv 0 J).map f := MvPolynomial.pderiv_map
  have hone : MvPolynomial.pderiv 1 (J.map f) =
      (MvPolynomial.pderiv 1 J).map f := MvPolynomial.pderiv_map
  unfold binaryProjectiveDerivativeResultant
  rw [hzero, hone, binaryDehomogenizeAtOne_map,
    binaryDehomogenizeAtOne_map, Polynomial.resultant_map_map]

/-- A prime avoiding the fixed projective derivative resultant is a genuine
good-reduction certificate: the affine dehomogenization modulo the prime is
squarefree and has degree at least `j - 1`. -/
theorem squarefree_dehom_map_and_degree_of_projectiveResultant_not_dvd
    (p j : ℕ) [Fact p.Prime] (J : MvPolynomial (Fin 2) ℤ)
    (hhom : J.IsHomogeneous j) (hj : 3 ≤ j)
    (hgood : ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j) :
    let P := binaryDehomogenizeAtOne
      (J.map (Int.castRingHom (ZMod p)))
    Squarefree P ∧ j - 1 ≤ P.natDegree := by
  let f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let Jp : MvPolynomial (Fin 2) (ZMod p) := J.map f
  let P : Polynomial (ZMod p) := binaryDehomogenizeAtOne Jp
  let A : Polynomial (ZMod p) :=
    binaryDehomogenizeAtOne (MvPolynomial.pderiv 0 Jp)
  let B : Polynomial (ZMod p) :=
    binaryDehomogenizeAtOne (MvPolynomial.pderiv 1 Jp)
  have hhomP : Jp.IsHomogeneous j := hhom.map f
  have hAhom : (MvPolynomial.pderiv 0 Jp).IsHomogeneous (j - 1) :=
    hhomP.pderiv
  have hBhom : (MvPolynomial.pderiv 1 Jp).IsHomogeneous (j - 1) :=
    hhomP.pderiv
  have hAdeg : A.natDegree ≤ j - 1 :=
    (natDegree_binaryDehomogenizeAtOne_le_totalDegree _).trans
      hAhom.totalDegree_le
  have hBdeg : B.natDegree ≤ j - 1 :=
    (natDegree_binaryDehomogenizeAtOne_le_totalDegree _).trans
      hBhom.totalDegree_le
  have hcast : (f (binaryProjectiveDerivativeResultant J j)) ≠ 0 := by
    intro hzero
    apply hgood
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (binaryProjectiveDerivativeResultant J j) p).mp hzero
  have hres : Polynomial.resultant A B (j - 1) (j - 1) ≠ 0 := by
    change binaryProjectiveDerivativeResultant Jp j ≠ 0
    rw [binaryProjectiveDerivativeResultant_map]
    exact hcast
  obtain ⟨u, v, -, -, huv⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant A B hAdeg hBdeg
      (by omega : j - 1 ≠ 0 ∨ j - 1 ≠ 0)
  have hcopAB : IsCoprime A B := by
    let res : ZMod p := Polynomial.resultant A B (j - 1) (j - 1)
    refine ⟨Polynomial.C res⁻¹ * u, Polynomial.C res⁻¹ * v, ?_⟩
    calc
      (Polynomial.C res⁻¹ * u) * A +
          (Polynomial.C res⁻¹ * v) * B =
        Polynomial.C res⁻¹ * (A * u + B * v) := by ring
      _ = Polynomial.C res⁻¹ * Polynomial.C res := by rw [huv]
      _ = 1 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hres, map_one]
  have hAderiv : A = P.derivative := by
    exact binaryDehomogenizeAtOne_pderiv_zero Jp
  have hBformula :
      B = Polynomial.C (j : ZMod p) * P - Polynomial.X * P.derivative := by
    exact binaryDehomogenizeAtOne_pderiv_one_of_isHomogeneous Jp j hhomP
  have hcopP : IsCoprime P P.derivative := by
    rcases hcopAB with ⟨u, v, huv⟩
    have huv' :
        u * P.derivative +
            v * (Polynomial.C (j : ZMod p) * P -
              Polynomial.X * P.derivative) = 1 := by
      simpa only [hAderiv, hBformula] using huv
    refine ⟨v * Polynomial.C (j : ZMod p), u - v * Polynomial.X, ?_⟩
    calc
      (v * Polynomial.C (j : ZMod p)) * P +
          (u - v * Polynomial.X) * P.derivative =
        u * P.derivative +
          v * (Polynomial.C (j : ZMod p) * P -
            Polynomial.X * P.derivative) := by ring
      _ = 1 := huv'
  have hsq : Squarefree P :=
    ((Polynomial.separable_def P).mpr hcopP).squarefree
  have hdegree : j - 1 ≤ P.natDegree := by
    by_contra hnot
    have hPlt : P.natDegree < j - 1 := Nat.lt_of_not_ge hnot
    have hAlt : A.natDegree < j - 1 := by
      rw [hAderiv]
      exact (Polynomial.natDegree_derivative_le P).trans_lt (by omega)
    have hCP :
        (Polynomial.C (j : ZMod p) * P).natDegree < j - 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans_lt hPlt
    have hXP : (Polynomial.X * P.derivative).natDegree < j - 1 := by
      by_cases hder : P.derivative = 0
      · rw [hder, mul_zero]
        simp only [Polynomial.natDegree_zero]
        omega
      · rw [Polynomial.natDegree_X_mul hder]
        have hderdeg := Polynomial.natDegree_derivative_le P
        omega
    have hBlt : B.natDegree < j - 1 := by
      rw [hBformula]
      exact (Polynomial.natDegree_sub_le _ _).trans_lt (max_lt hCP hXP)
    exact hres (Polynomial.resultant_eq_zero_of_lt_lt
      A B (j - 1) (j - 1) hAlt hBlt)
  exact ⟨hsq, hdegree⟩

end
end PellPaper
