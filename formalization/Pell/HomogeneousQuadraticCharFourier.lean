import Pell.ZModFourierRectangle
import Mathlib.NumberTheory.GaussSum
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Fourier coefficients of homogeneous quadratic-character sums

For a homogeneous binary form of odd degree over an odd prime field, the
negative, unnormalised double Fourier coefficient is an exact negative
quadratic Gauss factor times a one-variable character sum.  The extra term
in the formula is the exact contribution of the projective point `y = 0`.

No estimate for the remaining one-variable character sum is assumed here.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

private def complexQuadraticChar (p : ℕ) [Fact p.Prime] :
    MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

private theorem complexQuadraticChar_isQuadratic
    (p : ℕ) [Fact p.Prime] : (complexQuadraticChar p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

private theorem eval_scale_of_isHomogeneous
    {R σ : Type*} [CommSemiring R] [Fintype σ]
    (J : MvPolynomial σ R) (j : ℕ) (hJ : J.IsHomogeneous j)
    (t : R) (v : σ → R) :
    MvPolynomial.eval (fun i => t * v i) J =
      t ^ j * MvPolynomial.eval v J := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : (∑ i, d i) = j := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hJ (MvPolynomial.mem_support_iff.mp hd)
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ac_rfl

private theorem sum_binary_eq_slope_sum_add_axis
    {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
    [AddCommMonoid A] (G : F → F → A) (hG : G 0 0 = 0) :
    (∑ x : F, ∑ y : F, G x y) =
      (∑ r : F, ∑ y : F, G (r * y) y) + ∑ x : F, G x 0 := by
  calc
    (∑ x : F, ∑ y : F, G x y) =
        ∑ x : F, ((∑ y ∈ (Finset.univ : Finset F).erase 0, G x y) + G x 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (Finset.sum_erase_add Finset.univ (G x) (Finset.mem_univ 0)).symm
    _ = (∑ x : F, ∑ y ∈ (Finset.univ : Finset F).erase 0, G x y) +
        ∑ x : F, G x 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ y ∈ (Finset.univ : Finset F).erase 0, ∑ x : F, G x y) +
        ∑ x : F, G x 0 := by
      rw [Finset.sum_comm]
    _ = (∑ y ∈ (Finset.univ : Finset F).erase 0,
          ∑ r : F, G (r * y) y) + ∑ x : F, G x 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
      calc
        (∑ x : F, G x y) = ∑ r : F, G (y * r) y :=
          ((mulLeft_bijective₀ y hy0).sum_comp (fun x => G x y)).symm
        _ = ∑ r : F, G (r * y) y := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [mul_comm]
    _ = (∑ r : F, ∑ y ∈ (Finset.univ : Finset F).erase 0,
          G (r * y) y) + ∑ x : F, G x 0 := by
      rw [Finset.sum_comm]
    _ = (∑ r : F, ∑ y : F, G (r * y) y) + ∑ x : F, G x 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _hr
      simpa only [mul_zero, hG, add_zero] using
        (Finset.sum_erase_add Finset.univ (fun y => G (r * y) y)
          (Finset.mem_univ 0))

private theorem quadraticGaussShift_neg
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c : ZMod p) :
    (∑ y : ZMod p,
      complexQuadraticChar p y * ZMod.stdAddChar (-c * y)) =
      gaussSum (complexQuadraticChar p)
          ((ZMod.stdAddChar : AddChar (ZMod p) ℂ)⁻¹) *
        complexQuadraticChar p c := by
  let χ := complexQuadraticChar p
  let ψ : AddChar (ZMod p) ℂ :=
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ)⁻¹
  have hpchar : ringChar (ZMod p) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hp
  have hχquad : χ.IsQuadratic := complexQuadraticChar_isQuadratic p
  have hcast : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hχne : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff hcast).mpr
      (quadraticChar_ne_one hpchar)
  by_cases hc : c = 0
  · subst c
    change (∑ y : ZMod p, χ y * ZMod.stdAddChar (-0 * y)) =
      gaussSum χ ψ * χ 0
    simpa only [neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one,
      MulChar.map_zero, mul_zero] using χ.sum_eq_zero_of_ne_one hχne
  · let u : (ZMod p)ˣ := Units.mk0 c hc
    change (∑ y : ZMod p, χ y * ZMod.stdAddChar (-c * y)) =
      gaussSum χ ψ * χ c
    calc
      (∑ y : ZMod p, χ y * ZMod.stdAddChar (-c * y)) =
          gaussSum χ (ψ.mulShift (u : ZMod p)) := by
        apply Finset.sum_congr rfl
        intro y _hy
        simp only [AddChar.mulShift_apply, ψ, AddChar.inv_apply, u]
        rw [show ((Units.mk0 c hc : (ZMod p)ˣ) : ZMod p) = c by rfl]
        rw [neg_mul]
      _ = χ⁻¹ (u : ZMod p) * gaussSum χ ψ :=
        gaussSum_mulShift_eq χ ψ u
      _ = gaussSum χ ψ * χ c := by
        rw [hχquad.inv]
        change χ c * gaussSum χ ψ = gaussSum χ ψ * χ c
        ring

/-- The exact negative double Fourier coefficient of an odd-degree
homogeneous binary form.  The last character value is precisely the
`y = 0` contribution; in particular it vanishes if `a = 0` or if the
coefficient `J(1,0)` vanishes. -/
theorem zmodFourier2_quadraticChar_eval_binary_eq_gaussSum
    (p j : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (J : MvPolynomial (Fin 2) (ZMod p))
    (hJ : J.IsHomogeneous j) (hj : Odd j) (a b : ZMod p) :
    zmodFourier2 (fun x y =>
        (quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J) : ℂ)) a b =
      gaussSum
          ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
          ((ZMod.stdAddChar : AddChar (ZMod p) ℂ)⁻¹) *
        ((∑ r : ZMod p,
            (quadraticChar (ZMod p)
              (MvPolynomial.eval ![r, 1] J * (a * r + b)) : ℂ)) +
          (quadraticChar (ZMod p)
            (MvPolynomial.eval ![1, 0] J * a) : ℂ)) := by
  classical
  let χ := complexQuadraticChar p
  let τ := gaussSum χ ((ZMod.stdAddChar : AddChar (ZMod p) ℂ)⁻¹)
  have hχquad : χ.IsQuadratic := complexQuadraticChar_isQuadratic p
  have hjpos : 0 < j := hj.pos
  have hpow (y : ZMod p) : χ (y ^ j) = χ y := by
    rw [map_pow, ← χ.pow_apply' hjpos.ne' y, hχquad.pow_odd hj]
  have heval (r y : ZMod p) :
      MvPolynomial.eval ![r * y, y] J =
        y ^ j * MvPolynomial.eval ![r, 1] J := by
    have hv : ![r * y, y] = fun i => y * ![r, 1] i := by
      ext i
      fin_cases i <;> simp [mul_comm]
    rw [hv, eval_scale_of_isHomogeneous J j hJ]
  have heval_axis (x : ZMod p) :
      MvPolynomial.eval ![x, 0] J =
        x ^ j * MvPolynomial.eval ![1, 0] J := by
    have hv : ![x, 0] = fun i => x * ![1, 0] i := by
      ext i
      fin_cases i <;> simp
    rw [hv, eval_scale_of_isHomogeneous J j hJ]
  have heval_zero : MvPolynomial.eval ![(0 : ZMod p), 0] J = 0 := by
    simpa only [zero_mul, zero_pow hjpos.ne', zero_mul] using heval_axis 0
  let G : ZMod p → ZMod p → ℂ := fun x y =>
    χ (MvPolynomial.eval ![x, y] J) * ZMod.stdAddChar (-a * x - b * y)
  have hG : G 0 0 = 0 := by
    simp only [G, heval_zero, MulChar.map_zero, zero_mul]
  have hoff (r : ZMod p) :
      (∑ y : ZMod p, G (r * y) y) =
        τ * χ (MvPolynomial.eval ![r, 1] J * (a * r + b)) := by
    calc
      (∑ y : ZMod p, G (r * y) y) =
          ∑ y : ZMod p,
            χ (MvPolynomial.eval ![r, 1] J) *
              (χ y * ZMod.stdAddChar (-(a * r + b) * y)) := by
        apply Finset.sum_congr rfl
        intro y _hy
        simp only [G]
        rw [heval, map_mul, hpow]
        rw [show -a * (r * y) - b * y = -(a * r + b) * y by ring]
        ring
      _ = χ (MvPolynomial.eval ![r, 1] J) *
          (∑ y : ZMod p, χ y * ZMod.stdAddChar (-(a * r + b) * y)) := by
        rw [Finset.mul_sum]
      _ = χ (MvPolynomial.eval ![r, 1] J) *
          (τ * χ (a * r + b)) := by
        rw [quadraticGaussShift_neg p hp]
      _ = τ * χ (MvPolynomial.eval ![r, 1] J * (a * r + b)) := by
        rw [map_mul]
        ring
  have haxis :
      (∑ x : ZMod p, G x 0) =
        τ * χ (MvPolynomial.eval ![1, 0] J * a) := by
    calc
      (∑ x : ZMod p, G x 0) =
          ∑ x : ZMod p,
            χ (MvPolynomial.eval ![1, 0] J) *
              (χ x * ZMod.stdAddChar (-a * x)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        simp only [G]
        rw [heval_axis, map_mul, hpow]
        simp only [mul_zero, sub_zero]
        ring
      _ = χ (MvPolynomial.eval ![1, 0] J) *
          (∑ x : ZMod p, χ x * ZMod.stdAddChar (-a * x)) := by
        rw [Finset.mul_sum]
      _ = χ (MvPolynomial.eval ![1, 0] J) * (τ * χ a) := by
        rw [quadraticGaussShift_neg p hp]
      _ = τ * χ (MvPolynomial.eval ![1, 0] J * a) := by
        rw [map_mul]
        ring
  change (∑ x : ZMod p, ∑ y : ZMod p, G x y) =
    τ * ((∑ r : ZMod p,
      χ (MvPolynomial.eval ![r, 1] J * (a * r + b))) +
        χ (MvPolynomial.eval ![1, 0] J * a))
  rw [sum_binary_eq_slope_sum_add_axis G hG]
  simp_rw [hoff]
  rw [haxis, mul_add, Finset.mul_sum]

end

end PellPaper
