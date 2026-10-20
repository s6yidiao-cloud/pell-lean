import Pell.QuadraticFormProperEquivalence
import Pell.SquareParts
import Mathlib.Tactic

/-!
# The special quadratic surface form in shifted-square coordinates

This isolated algebraic module defines the two manuscript forms attached to
an integral generator satisfying `omega^2 = t*omega + c`, combines them at a
fixed primitive target vector, and records its exact discriminant and content.
It also isolates the squarefree scalar arithmetic needed after content
removal.  No explicit quadratic-field basis construction is imported here.
-/

namespace PellPaper

/-- The coefficient of `omega` in `(x0 + x1*omega)^2`. -/
def shiftedSquareSurfaceP (t : ℤ) (x : Fin 2 → ℤ) : ℤ :=
  2 * x 0 * x 1 + t * x 1 ^ 2

/-- The coefficient of `omega` in
`(x0 + x1*omega)^2 * omega` when `omega^2 = t*omega + c`. -/
def shiftedSquareSurfaceQ (t c : ℤ) (x : Fin 2 → ℤ) : ℤ :=
  x 0 ^ 2 + 2 * t * x 0 * x 1 + (c + t ^ 2) * x 1 ^ 2

/-- For a fixed target pair `y`, the quadratic form
`P_t(x)*y0 + Q_{t,c}(x)*y1`. -/
def shiftedSquareSurfaceForm (t c : ℤ) (y : Fin 2 → ℤ) :
    IntegralBinaryQuadraticForm where
  a := y 1
  b := 2 * y 0 + 2 * t * y 1
  c := t * y 0 + (c + t ^ 2) * y 1

@[simp]
theorem shiftedSquareSurfaceForm_eval (t c : ℤ) (x y : Fin 2 → ℤ) :
    (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
      shiftedSquareSurfaceP t x * y 0 +
        shiftedSquareSurfaceQ t c x * y 1 := by
  simp only [shiftedSquareSurfaceForm, IntegralBinaryQuadraticForm.eval,
    shiftedSquareSurfaceP, shiftedSquareSurfaceQ]
  ring

/-- The exact discriminant identity used by the fixed-target quadratic-form
argument. -/
theorem shiftedSquareSurfaceForm_discriminant (t c : ℤ) (y : Fin 2 → ℤ) :
    (shiftedSquareSurfaceForm t c y).discriminant =
      4 * (y 0 ^ 2 + t * y 0 * y 1 - c * y 1 ^ 2) := by
  simp only [shiftedSquareSurfaceForm,
    IntegralBinaryQuadraticForm.discriminant]
  ring

/-- The nonnegative gcd of all three coefficients of an integral binary
quadratic form. -/
def integralBinaryQuadraticFormContent (Q : IntegralBinaryQuadraticForm) : ℕ :=
  Int.gcd (Int.gcd Q.a Q.b : ℤ) Q.c

theorem integralBinaryQuadraticFormContent_dvd_a
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) ∣ Q.a := by
  exact (Int.gcd_dvd_left (Int.gcd Q.a Q.b : ℤ) Q.c).trans
    (Int.gcd_dvd_left Q.a Q.b)

theorem integralBinaryQuadraticFormContent_dvd_b
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) ∣ Q.b := by
  exact (Int.gcd_dvd_left (Int.gcd Q.a Q.b : ℤ) Q.c).trans
    (Int.gcd_dvd_right Q.a Q.b)

theorem integralBinaryQuadraticFormContent_dvd_c
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) ∣ Q.c := by
  exact Int.gcd_dvd_right (Int.gcd Q.a Q.b : ℤ) Q.c

/-- Divide all three coefficients by their common nonnegative content. -/
def integralBinaryQuadraticFormPrimitivePart
    (Q : IntegralBinaryQuadraticForm) : IntegralBinaryQuadraticForm where
  a := Q.a / (integralBinaryQuadraticFormContent Q : ℤ)
  b := Q.b / (integralBinaryQuadraticFormContent Q : ℤ)
  c := Q.c / (integralBinaryQuadraticFormContent Q : ℤ)

theorem integralBinaryQuadraticFormContent_mul_primitivePart_a
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) *
        (integralBinaryQuadraticFormPrimitivePart Q).a = Q.a := by
  change (integralBinaryQuadraticFormContent Q : ℤ) *
      (Q.a / (integralBinaryQuadraticFormContent Q : ℤ)) = Q.a
  rw [mul_comm]
  exact Int.ediv_mul_cancel (integralBinaryQuadraticFormContent_dvd_a Q)

theorem integralBinaryQuadraticFormContent_mul_primitivePart_b
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) *
        (integralBinaryQuadraticFormPrimitivePart Q).b = Q.b := by
  change (integralBinaryQuadraticFormContent Q : ℤ) *
      (Q.b / (integralBinaryQuadraticFormContent Q : ℤ)) = Q.b
  rw [mul_comm]
  exact Int.ediv_mul_cancel (integralBinaryQuadraticFormContent_dvd_b Q)

theorem integralBinaryQuadraticFormContent_mul_primitivePart_c
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) *
        (integralBinaryQuadraticFormPrimitivePart Q).c = Q.c := by
  change (integralBinaryQuadraticFormContent Q : ℤ) *
      (Q.c / (integralBinaryQuadraticFormContent Q : ℤ)) = Q.c
  rw [mul_comm]
  exact Int.ediv_mul_cancel (integralBinaryQuadraticFormContent_dvd_c Q)

/-- Removing a positive coefficient content produces a primitive integral
binary quadratic form in the existing `IntegralBinaryQuadraticForm` sense. -/
theorem integralBinaryQuadraticFormPrimitivePart_primitive
    (Q : IntegralBinaryQuadraticForm)
    (hcontent : 0 < integralBinaryQuadraticFormContent Q) :
    (integralBinaryQuadraticFormPrimitivePart Q).Primitive := by
  intro z hza hzb hzc
  let g := integralBinaryQuadraticFormContent Q
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hcontent.ne'
  have hza' : (g : ℤ) * z ∣ Q.a := by
    rw [← integralBinaryQuadraticFormContent_mul_primitivePart_a Q]
    exact mul_dvd_mul_left (g : ℤ) hza
  have hzb' : (g : ℤ) * z ∣ Q.b := by
    rw [← integralBinaryQuadraticFormContent_mul_primitivePart_b Q]
    exact mul_dvd_mul_left (g : ℤ) hzb
  have hzc' : (g : ℤ) * z ∣ Q.c := by
    rw [← integralBinaryQuadraticFormContent_mul_primitivePart_c Q]
    exact mul_dvd_mul_left (g : ℤ) hzc
  have hzab : (g : ℤ) * z ∣ (Int.gcd Q.a Q.b : ℤ) :=
    Int.dvd_coe_gcd hza' hzb'
  have hzg : (g : ℤ) * z ∣ (g : ℤ) := by
    exact Int.dvd_coe_gcd hzab hzc'
  obtain ⟨q, hq⟩ := hzg
  apply isUnit_iff_dvd_one.mpr
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ hg0
  calc
    (g : ℤ) * 1 = (g : ℤ) := by ring
    _ = ((g : ℤ) * z) * q := hq
    _ = (g : ℤ) * (z * q) := by ring

/-- The discriminant scales by the square of the removed content. -/
theorem integralBinaryQuadraticFormPrimitivePart_discriminant_scale
    (Q : IntegralBinaryQuadraticForm) :
    (integralBinaryQuadraticFormContent Q : ℤ) ^ 2 *
        (integralBinaryQuadraticFormPrimitivePart Q).discriminant =
      Q.discriminant := by
  simp only [IntegralBinaryQuadraticForm.discriminant]
  rw [← integralBinaryQuadraticFormContent_mul_primitivePart_a Q,
    ← integralBinaryQuadraticFormContent_mul_primitivePart_b Q,
    ← integralBinaryQuadraticFormContent_mul_primitivePart_c Q]
  ring

/-- A primitive target pair makes the special surface form nonzero, hence its
three-coefficient content is positive. -/
theorem shiftedSquareSurfaceForm_content_pos
    (t c : ℤ) (y : Fin 2 → ℤ)
    (hy : IsCoprime (y 0) (y 1)) :
    0 < integralBinaryQuadraticFormContent
      (shiftedSquareSurfaceForm t c y) := by
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨habCastZero, _⟩ := Int.gcd_eq_zero_iff.mp hzero
  have habZero : Int.gcd
      (shiftedSquareSurfaceForm t c y).a
      (shiftedSquareSurfaceForm t c y).b = 0 := by
    exact_mod_cast habCastZero
  obtain ⟨haZero, hbZero⟩ := Int.gcd_eq_zero_iff.mp habZero
  have hy1 : y 1 = 0 := by
    simpa only [shiftedSquareSurfaceForm] using haZero
  have hy0 : y 0 = 0 := by
    simp only [shiftedSquareSurfaceForm, hy1, mul_zero, add_zero] at hbZero
    omega
  obtain ⟨u, v, huv⟩ := hy
  rw [hy0, hy1] at huv
  norm_num at huv

/-- Primitivity of the fixed target pair forces the surface-form content to
divide two.  The stronger statement holds for every integer `t`. -/
theorem shiftedSquareSurfaceForm_content_dvd_two
    (t c : ℤ) (y : Fin 2 → ℤ)
    (hy : IsCoprime (y 0) (y 1)) :
    integralBinaryQuadraticFormContent (shiftedSquareSurfaceForm t c y) ∣ 2 := by
  let g := integralBinaryQuadraticFormContent
    (shiftedSquareSurfaceForm t c y)
  have hgy1 : (g : ℤ) ∣ y 1 := by
    simpa only [g, shiftedSquareSurfaceForm] using
      integralBinaryQuadraticFormContent_dvd_a
        (shiftedSquareSurfaceForm t c y)
  have hgb : (g : ℤ) ∣ 2 * y 0 + 2 * t * y 1 := by
    simpa only [g, shiftedSquareSurfaceForm] using
      integralBinaryQuadraticFormContent_dvd_b
        (shiftedSquareSurfaceForm t c y)
  have hgtwoY0 : (g : ℤ) ∣ 2 * y 0 := by
    have hsubtract := dvd_sub hgb (hgy1.mul_left (2 * t))
    rw [show 2 * y 0 + 2 * t * y 1 - (2 * t) * y 1 =
      2 * y 0 by ring] at hsubtract
    exact hsubtract
  obtain ⟨u, v, huv⟩ := hy
  have htwoInt : (g : ℤ) ∣ (2 : ℤ) := by
    have hsum := dvd_add (hgtwoY0.mul_left u)
      (hgy1.mul_left (2 * v))
    have heq : u * (2 * y 0) + (2 * v) * y 1 = 2 := by
      nlinarith [huv]
    rwa [heq] at hsum
  exact_mod_cast htwoInt

/-- In particular, under the manuscript restriction `t in {0,1}`, the
coefficient content is at most two. -/
theorem shiftedSquareSurfaceForm_content_le_two_of_t_zero_or_one
    (t c : ℤ) (y : Fin 2 → ℤ)
    (hy : IsCoprime (y 0) (y 1)) (_ht : t = 0 ∨ t = 1) :
    integralBinaryQuadraticFormContent (shiftedSquareSurfaceForm t c y) ≤ 2 := by
  exact Nat.le_of_dvd (by decide)
    (shiftedSquareSurfaceForm_content_dvd_two t c y hy)

/-- Squarefreeness absorbs the only possible unpaired prime exponent:
`ell^2 | w*C0^2` implies `ell | C0`. -/
theorem dvd_of_sq_dvd_squarefree_mul_sq
    {ell w C₀ : ℕ} (hwpos : 0 < w) (hw : Squarefree w)
    (hdiv : ell ^ 2 ∣ w * C₀ ^ 2) :
    ell ∣ C₀ := by
  by_cases hC₀0 : C₀ = 0
  · simp [hC₀0]
  have hright0 : w * C₀ ^ 2 ≠ 0 :=
    mul_ne_zero hwpos.ne' (pow_ne_zero 2 hC₀0)
  have hell0 : ell ≠ 0 := by
    intro hell
    subst ell
    have hz : (0 : ℕ) ∣ w * C₀ ^ 2 := by simpa using hdiv
    exact hright0 (zero_dvd_iff.mp hz)
  apply (Nat.factorization_le_iff_dvd hell0 hC₀0).mp
  intro p
  have hp :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hell0) hright0).mpr hdiv p
  have hwp : w.factorization p ≤ 1 := hw.natFactorization_le_one p
  simp only [Nat.factorization_pow,
    Nat.factorization_mul hwpos.ne' (pow_ne_zero 2 hC₀0),
    Finsupp.smul_apply, Finsupp.add_apply, nsmul_eq_mul] at hp
  omega

/-- A positive square times a squarefree integer greater than one is not a
square. -/
theorem not_isSquare_squarefree_mul_sq
    {w k : ℕ} (hw : Squarefree w) (hwone : 1 < w) (hk : 0 < k) :
    ¬ IsSquare (w * k ^ 2) := by
  intro hsquare
  obtain ⟨s, hs⟩ := hsquare
  have hmpos : 0 < w * k ^ 2 :=
    Nat.mul_pos (lt_trans Nat.zero_lt_one hwone) (pow_pos hk 2)
  have hspos : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro hs0
    rw [hs, hs0] at hmpos
    norm_num at hmpos
  have hone : Squarefree (1 : ℕ) := squarefree_one
  obtain ⟨_, hw_eq_one⟩ := square_part_decomposition_unique
    hspos (by decide : 0 < (1 : ℕ)) hk (lt_trans Nat.zero_lt_one hwone)
    (by simpa only [pow_two, mul_one] using hs)
    (by simp only [pow_two, mul_comm]) hone hw
  omega

/-- After removing its content, the fixed-target surface form is primitive
and has positive nonsquare discriminant.  The square part is exactly either
`2*(C0/ell)` or `C0/ell`, according as the content is one or two. -/
theorem shiftedSquareSurfacePrimitivePart_discriminant_pos_not_isSquare
    (t c : ℤ) (y : Fin 2 → ℤ)
    (hy : IsCoprime (y 0) (y 1)) (ht : t = 0 ∨ t = 1)
    {ell w C₀ : ℕ}
    (hell : 0 < ell) (hw : Squarefree w) (hwone : 1 < w)
    (hC₀ : 0 < C₀) (hdiv : ell ^ 2 ∣ w * C₀ ^ 2)
    (hnorm :
      y 0 ^ 2 + t * y 0 * y 1 - c * y 1 ^ 2 =
        ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ)) :
    (integralBinaryQuadraticFormPrimitivePart
        (shiftedSquareSurfaceForm t c y)).Primitive ∧
      ell ∣ C₀ ∧
      0 < (integralBinaryQuadraticFormPrimitivePart
        (shiftedSquareSurfaceForm t c y)).discriminant ∧
      ¬ IsSquare (integralBinaryQuadraticFormPrimitivePart
        (shiftedSquareSurfaceForm t c y)).discriminant ∧
      ∃ s : ℕ, 0 < s ∧
        (s = 2 * (C₀ / ell) ∨ s = C₀ / ell) ∧
        (integralBinaryQuadraticFormPrimitivePart
            (shiftedSquareSurfaceForm t c y)).discriminant =
          ((w * s ^ 2 : ℕ) : ℤ) := by
  let Q := shiftedSquareSurfaceForm t c y
  let g := integralBinaryQuadraticFormContent Q
  let R := integralBinaryQuadraticFormPrimitivePart Q
  have hgpos : 0 < g := by
    exact shiftedSquareSurfaceForm_content_pos t c y hy
  have hgle : g ≤ 2 := by
    exact shiftedSquareSurfaceForm_content_le_two_of_t_zero_or_one
      t c y hy ht
  have hgcases : g = 1 ∨ g = 2 := by omega
  have hellC₀ : ell ∣ C₀ :=
    dvd_of_sq_dvd_squarefree_mul_sq
      (lt_trans Nat.zero_lt_one hwone) hw hdiv
  have hkpos : 0 < C₀ / ell :=
    Nat.div_pos (Nat.le_of_dvd hC₀ hellC₀) hell
  have hraw : Q.discriminant =
      ((4 * (w * (C₀ / ell) ^ 2) : ℕ) : ℤ) := by
    dsimp only [Q]
    rw [shiftedSquareSurfaceForm_discriminant, hnorm]
    norm_num
  have hscale : (g : ℤ) ^ 2 * R.discriminant = Q.discriminant := by
    exact integralBinaryQuadraticFormPrimitivePart_discriminant_scale Q
  have hrepresentation : ∃ s : ℕ, 0 < s ∧
      (s = 2 * (C₀ / ell) ∨ s = C₀ / ell) ∧
      R.discriminant = ((w * s ^ 2 : ℕ) : ℤ) := by
    rcases hgcases with hg | hg
    · refine ⟨2 * (C₀ / ell), Nat.mul_pos (by decide) hkpos,
        Or.inl rfl, ?_⟩
      rw [hg, hraw] at hscale
      norm_num at hscale ⊢
      nlinarith
    · refine ⟨C₀ / ell, hkpos, Or.inr rfl, ?_⟩
      rw [hg, hraw] at hscale
      norm_num at hscale ⊢
      nlinarith
  obtain ⟨s, hs, hschoice, hdisc⟩ := hrepresentation
  have hdiscpos : 0 < R.discriminant := by
    rw [hdisc]
    exact_mod_cast Nat.mul_pos (lt_trans Nat.zero_lt_one hwone) (pow_pos hs 2)
  have hdiscNotSquare : ¬ IsSquare R.discriminant := by
    rw [hdisc]
    simpa only [Int.isSquare_natCast_iff] using
      (not_isSquare_squarefree_mul_sq hw hwone hs)
  change R.Primitive ∧ ell ∣ C₀ ∧ 0 < R.discriminant ∧
    ¬ IsSquare R.discriminant ∧ ∃ s : ℕ, 0 < s ∧
      (s = 2 * (C₀ / ell) ∨ s = C₀ / ell) ∧
      R.discriminant = ((w * s ^ 2 : ℕ) : ℤ)
  exact ⟨integralBinaryQuadraticFormPrimitivePart_primitive Q hgpos,
    hellC₀, hdiscpos, hdiscNotSquare,
    s, hs, hschoice, hdisc⟩

end PellPaper
