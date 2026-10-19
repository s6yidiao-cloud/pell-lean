import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Pell.ClassAverage

/-!
# Primitive integral binary quadratic forms and proper equivalence

This isolated module gives the literal source-side object underlying the
manuscript's phrase "proper equivalence classes of primitive indefinite binary
quadratic forms".  It deliberately stops before the classical correspondence
with ideals in a quadratic order: Mathlib currently supplies ideal class groups
and abstract quadratic forms, but no API for this arithmetic correspondence or
for finiteness/cardinality of the proper-equivalence quotient.

The quotient defined here is therefore a genuine form-class type, not yet a
replacement for `NumberField.classNumber`.
-/

namespace PellPaper

open scoped MatrixGroups

/-- An integral binary quadratic form, written `a X^2 + b X Y + c Y^2`. -/
structure IntegralBinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

namespace IntegralBinaryQuadraticForm

/-- Evaluation of an integral binary quadratic form. -/
def eval (Q : IntegralBinaryQuadraticForm) (x y : ℤ) : ℤ :=
  Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- The classical discriminant `b^2 - 4ac`. -/
def discriminant (Q : IntegralBinaryQuadraticForm) : ℤ :=
  Q.b ^ 2 - 4 * Q.a * Q.c

/-- A form is primitive when its three coefficients have no nonunit common
integer divisor.  Over `ℤ` this is the usual primitivity condition. -/
def Primitive (Q : IntegralBinaryQuadraticForm) : Prop :=
  ∀ z : ℤ, z ∣ Q.a → z ∣ Q.b → z ∣ Q.c → IsUnit z

/-- Proper substitution by a determinant-one integral matrix.  The convention
is `Q.transform g = Q ∘ g` on column vectors. -/
def properTransform (Q : IntegralBinaryQuadraticForm) (g : SL(2, ℤ)) :
    IntegralBinaryQuadraticForm where
  a := Q.a * g 0 0 ^ 2 + Q.b * g 0 0 * g 1 0 + Q.c * g 1 0 ^ 2
  b := 2 * Q.a * g 0 0 * g 0 1 + Q.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) +
    2 * Q.c * g 1 0 * g 1 1
  c := Q.a * g 0 1 ^ 2 + Q.b * g 0 1 * g 1 1 + Q.c * g 1 1 ^ 2

@[ext]
theorem ext {Q R : IntegralBinaryQuadraticForm}
    (ha : Q.a = R.a) (hb : Q.b = R.b) (hc : Q.c = R.c) : Q = R := by
  cases Q
  cases R
  simp_all

@[simp]
theorem eval_properTransform (Q : IntegralBinaryQuadraticForm) (g : SL(2, ℤ))
    (x y : ℤ) :
    (Q.properTransform g).eval x y =
      Q.eval (g 0 0 * x + g 0 1 * y) (g 1 0 * x + g 1 1 * y) := by
  simp only [properTransform, eval]
  ring

/-- Proper substitutions preserve the discriminant exactly. -/
theorem discriminant_properTransform (Q : IntegralBinaryQuadraticForm) (g : SL(2, ℤ)) :
    (Q.properTransform g).discriminant = Q.discriminant := by
  have hg := g.property
  rw [Matrix.det_fin_two] at hg
  calc
    (Q.properTransform g).discriminant =
        Q.discriminant * (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 := by
          simp only [properTransform, discriminant]
          ring
    _ = Q.discriminant := by simp [hg]

@[simp]
theorem properTransform_one (Q : IntegralBinaryQuadraticForm) :
    Q.properTransform 1 = Q := by
  ext <;> simp [properTransform]

/-- The substitution convention defines a right action of `SL(2, ℤ)` on
integral binary quadratic forms. -/
theorem properTransform_mul (Q : IntegralBinaryQuadraticForm) (g h : SL(2, ℤ)) :
    (Q.properTransform g).properTransform h = Q.properTransform (g * h) := by
  ext <;>
    simp only [properTransform, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- Any common divisor of the coefficients remains a common divisor after a
proper substitution. -/
theorem common_dvd_properTransform {z : ℤ} (Q : IntegralBinaryQuadraticForm)
    (g : SL(2, ℤ)) (ha : z ∣ Q.a) (hb : z ∣ Q.b) (hc : z ∣ Q.c) :
    z ∣ (Q.properTransform g).a ∧ z ∣ (Q.properTransform g).b ∧
      z ∣ (Q.properTransform g).c := by
  rcases ha with ⟨a', ha⟩
  rcases hb with ⟨b', hb⟩
  rcases hc with ⟨c', hc⟩
  constructor
  · rw [properTransform, ha, hb, hc]
    exact ⟨a' * g 0 0 ^ 2 + b' * g 0 0 * g 1 0 + c' * g 1 0 ^ 2, by ring⟩
  constructor
  · rw [properTransform, ha, hb, hc]
    exact ⟨2 * a' * g 0 0 * g 0 1 + b' * (g 0 0 * g 1 1 + g 0 1 * g 1 0) +
      2 * c' * g 1 0 * g 1 1, by ring⟩
  · rw [properTransform, ha, hb, hc]
    exact ⟨a' * g 0 1 ^ 2 + b' * g 0 1 * g 1 1 + c' * g 1 1 ^ 2, by ring⟩

/-- Proper substitutions preserve and reflect primitivity. -/
theorem primitive_properTransform_iff (Q : IntegralBinaryQuadraticForm) (g : SL(2, ℤ)) :
    (Q.properTransform g).Primitive ↔ Q.Primitive := by
  constructor
  · intro h z ha hb hc
    exact h z (common_dvd_properTransform Q g ha hb hc).1
      (common_dvd_properTransform Q g ha hb hc).2.1
      (common_dvd_properTransform Q g ha hb hc).2.2
  · intro h z ha hb hc
    have hback : (Q.properTransform g).properTransform g⁻¹ = Q := by
      rw [properTransform_mul, mul_inv_cancel, properTransform_one]
    have hdiv := common_dvd_properTransform (Q.properTransform g) g⁻¹ ha hb hc
    apply h z
    · rw [← hback]
      exact hdiv.1
    · rw [← hback]
      exact hdiv.2.1
    · rw [← hback]
      exact hdiv.2.2

/-- Primitive integral binary quadratic forms of the fixed discriminant `D`. -/
def PrimitiveBinaryQuadraticForms (D : ℤ) :=
  {Q : IntegralBinaryQuadraticForm // Q.Primitive ∧ Q.discriminant = D}

/-- Proper substitution restricted to primitive forms of a fixed discriminant. -/
def properTransformAt {D : ℤ} (Q : PrimitiveBinaryQuadraticForms D) (g : SL(2, ℤ)) :
    PrimitiveBinaryQuadraticForms D :=
  ⟨Q.1.properTransform g,
    (primitive_properTransform_iff Q.1 g).mpr Q.2.1,
    (discriminant_properTransform Q.1 g).trans Q.2.2⟩

@[simp]
theorem properTransformAt_one {D : ℤ} (Q : PrimitiveBinaryQuadraticForms D) :
    properTransformAt Q 1 = Q := by
  apply Subtype.ext
  exact properTransform_one Q.1

theorem properTransformAt_mul {D : ℤ} (Q : PrimitiveBinaryQuadraticForms D)
    (g h : SL(2, ℤ)) :
    properTransformAt (properTransformAt Q g) h = properTransformAt Q (g * h) := by
  apply Subtype.ext
  exact properTransform_mul Q.1 g h

/-- The classical proper-equivalence relation on primitive integral binary
quadratic forms: a form is changed by a matrix in `SL(2, ℤ)`. -/
def ProperEquivalent {D : ℤ} (Q R : PrimitiveBinaryQuadraticForms D) : Prop :=
  ∃ g : SL(2, ℤ), properTransformAt Q g = R

theorem properEquivalent_refl {D : ℤ} (Q : PrimitiveBinaryQuadraticForms D) :
    ProperEquivalent Q Q :=
  ⟨1, properTransformAt_one Q⟩

theorem properEquivalent_symm {D : ℤ} {Q R : PrimitiveBinaryQuadraticForms D}
    (hQR : ProperEquivalent Q R) : ProperEquivalent R Q := by
  rcases hQR with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, properTransformAt_mul, mul_inv_cancel, properTransformAt_one]

theorem properEquivalent_trans {D : ℤ} {Q R S : PrimitiveBinaryQuadraticForms D}
    (hQR : ProperEquivalent Q R) (hRS : ProperEquivalent R S) : ProperEquivalent Q S := by
  rcases hQR with ⟨g, hg⟩
  rcases hRS with ⟨h, hh⟩
  refine ⟨g * h, ?_⟩
  rw [← properTransformAt_mul, hg, hh]

/-- The setoid whose quotient is the source's proper form-class set. -/
def properEquivalenceSetoid (D : ℤ) : Setoid (PrimitiveBinaryQuadraticForms D) where
  r := ProperEquivalent
  iseqv := ⟨properEquivalent_refl, properEquivalent_symm, properEquivalent_trans⟩

/-- Proper equivalence classes of primitive integral binary quadratic forms of
discriminant `D`.  For `0 < D`, this is the literal form-class type occurring
in the manuscript; finiteness and its comparison to ideal classes are not
provided here. -/
def ProperFormClass (D : ℤ) : Type :=
  Quotient (properEquivalenceSetoid D)

/-- The class represented by a primitive form. -/
def PrimitiveBinaryQuadraticForms.toProperFormClass {D : ℤ}
    (Q : PrimitiveBinaryQuadraticForms D) : ProperFormClass D :=
  Quotient.mk _ Q

/-- Properly equivalent forms define the same proper form class. -/
theorem PrimitiveBinaryQuadraticForms.toProperFormClass_eq_of_properEquivalent
    {D : ℤ} {Q R : PrimitiveBinaryQuadraticForms D} (h : ProperEquivalent Q R) :
    PrimitiveBinaryQuadraticForms.toProperFormClass Q =
      PrimitiveBinaryQuadraticForms.toProperFormClass R :=
  Quotient.sound h

/-- Equality in the quotient is exactly classical proper equivalence of the
chosen representatives. -/
theorem PrimitiveBinaryQuadraticForms.toProperFormClass_eq_iff
    {D : ℤ} {Q R : PrimitiveBinaryQuadraticForms D} :
    PrimitiveBinaryQuadraticForms.toProperFormClass Q =
        PrimitiveBinaryQuadraticForms.toProperFormClass R ↔ ProperEquivalent Q R := by
  constructor
  · exact Quotient.exact
  · exact PrimitiveBinaryQuadraticForms.toProperFormClass_eq_of_properEquivalent

/-- The primitive form `[1, 1, -D/4]` in the `D ≡ 1 (mod 4)` branch. -/
def principalFormOneModFour (D : ℕ) : IntegralBinaryQuadraticForm where
  a := 1
  b := 1
  c := -(D / 4 : ℤ)

/-- The primitive form `[1, 0, -d]` of discriminant `4d`. -/
def principalFormFourMul (d : ℕ) : IntegralBinaryQuadraticForm where
  a := 1
  b := 0
  c := -(d : ℤ)

theorem primitive_principalFormOneModFour (D : ℕ) :
    (principalFormOneModFour D).Primitive := by
  intro z hz _ _
  apply isUnit_of_dvd_one
  simpa [principalFormOneModFour] using hz

theorem primitive_principalFormFourMul (d : ℕ) :
    (principalFormFourMul d).Primitive := by
  intro z hz _ _
  apply isUnit_of_dvd_one
  simpa [principalFormFourMul] using hz

theorem discriminant_principalFormOneModFour (D : ℕ) (hDmod : D % 4 = 1) :
    (principalFormOneModFour D).discriminant = (D : ℤ) := by
  have hsplit := Nat.mod_add_div D 4
  have hD : D = 4 * (D / 4) + 1 := by
    omega
  have hD' : 1 + 4 * (D / 4) = D := by
    omega
  simp only [principalFormOneModFour, discriminant]
  norm_num
  exact_mod_cast hD'

theorem discriminant_principalFormFourMul (d : ℕ) :
    (principalFormFourMul d).discriminant = (4 * d : ℕ) := by
  simp [principalFormFourMul, discriminant]

/-- Every positive fundamental discriminant has a concrete primitive integral
binary quadratic form of that discriminant.  This only realizes the form side;
it makes no ideal-class correspondence or finiteness claim. -/
theorem nonempty_primitiveBinaryQuadraticForms_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    Nonempty (PrimitiveBinaryQuadraticForms (D : ℤ)) := by
  rcases hD.2 with hodd | hfour
  · refine ⟨⟨principalFormOneModFour D, primitive_principalFormOneModFour D,
      discriminant_principalFormOneModFour D hodd.2⟩⟩
  · obtain ⟨d, rfl, _hsq, _hmod⟩ := hfour
    refine ⟨⟨principalFormFourMul d, primitive_principalFormFourMul d, ?_⟩⟩
    simpa using discriminant_principalFormFourMul d

/-- Consequently, the proper form-class type is inhabited at every positive
fundamental discriminant. -/
theorem nonempty_properFormClass_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    Nonempty (ProperFormClass (D : ℤ)) := by
  obtain ⟨Q⟩ :=
    nonempty_primitiveBinaryQuadraticForms_of_positiveFundamentalDiscriminant D hD
  exact ⟨PrimitiveBinaryQuadraticForms.toProperFormClass Q⟩

end IntegralBinaryQuadraticForm

end PellPaper
