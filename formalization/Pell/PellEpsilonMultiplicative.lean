import Pell.QuadraticOrderPellRealEmbedding
import Mathlib.NumberTheory.Pell

/-!
# Multiplicative identities for the real Pell value

For a nonnegative radicand, the project quantity
`epsilon a = a.x + a.y * sqrt d` is the value of a Pell-order element under
the concrete real embedding.  This file packages that observation as a map to
real units and records its elementary multiplicative consequences.

The results concern only `Pell.Solution₁ d` and the explicitly chosen real
embedding.  They make no comparison with all units of the maximal order, no
statement about a regulator, and no unit-index assertion.
-/

namespace PellPaper

/-- The real-unit-valued homomorphism obtained by applying the chosen real
embedding to a norm-one Pell solution. -/
noncomputable def pellEpsilonUnitHom (d : ℤ) (hd : 0 ≤ d) :
    Pell.Solution₁ d →* ℝˣ :=
  (Units.map (rationalQuadraticAlgebraRealEmbedding d hd).toMonoidHom).comp
    ((Units.map (quadraticOrderPellEmbedding d).toMonoidHom).comp Unitary.toUnits)

/-- The underlying real value of `pellEpsilonUnitHom` is exactly `epsilon`. -/
@[simp]
theorem coe_pellEpsilonUnitHom (d : ℤ) (hd : 0 ≤ d) (a : Pell.Solution₁ d) :
    ((pellEpsilonUnitHom d hd a : ℝˣ) : ℝ) = epsilon a := by
  change rationalQuadraticAlgebraRealEmbedding d hd
      (quadraticOrderPellEmbedding d (a : ℤ√d)) = epsilon a
  exact rationalQuadraticAlgebraRealEmbedding_pellSolution hd a

/-- The real Pell value of a product is the product of the real Pell values. -/
@[simp]
theorem epsilon_mul {d : ℤ} (hd : 0 ≤ d) (a b : Pell.Solution₁ d) :
    epsilon (a * b) = epsilon a * epsilon b := by
  rw [← coe_pellEpsilonUnitHom d hd (a * b),
    ← coe_pellEpsilonUnitHom d hd a,
    ← coe_pellEpsilonUnitHom d hd b,
    (pellEpsilonUnitHom d hd).map_mul]
  rfl

/-- The real Pell value of the identity solution is one. -/
@[simp]
theorem epsilon_one (d : ℤ) (hd : 0 ≤ d) :
    epsilon (1 : Pell.Solution₁ d) = 1 := by
  rw [← coe_pellEpsilonUnitHom d hd (1 : Pell.Solution₁ d),
    (pellEpsilonUnitHom d hd).map_one]
  rfl

/-- The real Pell value of an inverse is the inverse real Pell value. -/
@[simp]
theorem epsilon_inv {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) :
    epsilon a⁻¹ = (epsilon a)⁻¹ := by
  rw [← coe_pellEpsilonUnitHom d hd a⁻¹,
    ← coe_pellEpsilonUnitHom d hd a,
    (pellEpsilonUnitHom d hd).map_inv]
  exact Units.val_inv_eq_inv_val _

/-- The real Pell value is nonzero for every norm-one solution at a
nonnegative radicand. -/
theorem epsilon_ne_zero {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) :
    epsilon a ≠ 0 := by
  rw [← coe_pellEpsilonUnitHom d hd a]
  exact (pellEpsilonUnitHom d hd a).ne_zero

/-- The real Pell value commutes with natural powers. -/
@[simp]
theorem epsilon_pow {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) (n : ℕ) :
    epsilon (a ^ n) = epsilon a ^ n := by
  rw [← coe_pellEpsilonUnitHom d hd (a ^ n),
    ← coe_pellEpsilonUnitHom d hd a,
    (pellEpsilonUnitHom d hd).map_pow]
  rfl

/-- The real Pell value commutes with integral powers. -/
@[simp]
theorem epsilon_zpow {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) (n : ℤ) :
    epsilon (a ^ n) = epsilon a ^ n := by
  rw [← coe_pellEpsilonUnitHom d hd (a ^ n),
    ← coe_pellEpsilonUnitHom d hd a,
    (pellEpsilonUnitHom d hd).map_zpow,
    Units.val_zpow_eq_zpow_val]

/-- Negating a Pell solution negates its real Pell value.  This identity does
not require a sign assumption on the radicand. -/
@[simp]
theorem epsilon_neg {d : ℤ} (a : Pell.Solution₁ d) :
    epsilon (-a) = -epsilon a := by
  change ((-a).x : ℝ) + ((-a).y : ℝ) * Real.sqrt (d : ℝ) =
    -((a.x : ℝ) + (a.y : ℝ) * Real.sqrt (d : ℝ))
  rw [Pell.Solution₁.x_neg, Pell.Solution₁.y_neg]
  push_cast
  ring

/-- The signed integral-power form combines the sign and power identities. -/
@[simp]
theorem epsilon_neg_zpow {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) (n : ℤ) :
    epsilon (-(a ^ n)) = -(epsilon a) ^ n := by
  rw [epsilon_neg, epsilon_zpow hd]

/-- A supplied fundamental Pell solution has real value strictly greater than
one under the positive real embedding. -/
theorem one_lt_epsilon_of_isFundamental {d : ℤ} {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) : 1 < epsilon a := by
  rw [epsilon]
  have hx : (1 : ℝ) < a.x := by exact_mod_cast ha.1
  have hy : (0 : ℝ) ≤ a.y := by exact_mod_cast ha.2.1.le
  have hroot : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  exact hx.trans_le (le_add_of_nonneg_right (mul_nonneg hy hroot))

/-- In particular, the real Pell value of a supplied fundamental solution is
positive. -/
theorem epsilon_pos_of_isFundamental {d : ℤ} {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) : 0 < epsilon a :=
  zero_lt_one.trans (one_lt_epsilon_of_isFundamental ha)

/-- Every integral power of a supplied fundamental solution has positive real
Pell value. -/
theorem epsilon_zpow_pos_of_isFundamental {d : ℤ} {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) (n : ℤ) : 0 < epsilon (a ^ n) := by
  rw [epsilon_zpow ha.d_pos.le]
  exact zpow_pos (epsilon_pos_of_isFundamental ha) n

end PellPaper
