import Pell.RealQuadraticFieldOddClassSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp

/-!
# Odd class-number parts and the genus weight

This file isolates the elementary genus algebra used in Corollary 1.2.
Mathlib's `ordCompl[2] n` is the largest odd divisor of a nonzero natural
number `n`, and `ArithmeticFunction.cardDistinctFactors` is the paper's
`omega` function.  The actual odd class-number summand is the one fixed in
`RealQuadraticFieldOddClassSum`.

The two genuinely arithmetic genus-theory statements are recorded as named
propositions, not axioms:

* the ordinary and proper-form class numbers have the same odd part;
* `2 ^ (omega D - 1)` divides the proper-form class number.

All consequences below those two interfaces, including the exact pointwise
bound `h_odd <= 2 * w(D) * h^+(D)`, are proved here.
-/

namespace PellPaper

noncomputable section

open scoped ArithmeticFunction.omega
open IntegralBinaryQuadraticForm

/-- The genus weight `w(D) = 2 ^ (-omega(D))`, represented without a
negative natural-number exponent. -/
def genusWeight (D : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (ω D)

theorem genusWeight_nonneg (D : ℕ) :
    0 ≤ genusWeight D := by
  unfold genusWeight
  positivity

theorem genusWeight_pos (D : ℕ) :
    0 < genusWeight D := by
  unfold genusWeight
  positivity

theorem genusWeight_le_one (D : ℕ) :
    genusWeight D ≤ 1 := by
  unfold genusWeight
  exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))

/-- The exact missing narrow/ordinary-class input for Corollary 1.2, stated
for the project's actual ordinary ideal class number and literal proper-form
class cardinality. -/
def ProperFormClassOddPartCompatibility : Prop :=
  ∀ (D : ℕ) (_hD : PositiveFundamentalDiscriminant D),
    positiveFundamentalDiscriminantOddClassNumber D =
      (ordCompl[2] (Nat.card (ProperFormClass (D : ℤ))) : ℕ)

/-- The exact missing genus-theory divisibility input for Corollary 1.2. -/
def ProperFormClassGenusDivisibility : Prop :=
  ∀ (D : ℕ) (_hD : PositiveFundamentalDiscriminant D),
    2 ^ (ω D - 1) ∣ Nat.card (ProperFormClass (D : ℤ))

/-- A stronger standard narrow-to-wide cardinality statement immediately
implies equality of odd parts. -/
theorem classNumberOddPart_eq_of_eq_or_eq_twice {h hplus : ℕ}
    (hcard : hplus = h ∨ hplus = 2 * h) :
    (ordCompl[2] h : ℕ) = (ordCompl[2] hplus : ℕ) := by
  rcases hcard with rfl | rfl
  · rfl
  · rw [Nat.ordCompl_mul]
    norm_num [Nat.ordCompl_self_pow Nat.prime_two]

/-- The natural-number core of the genus-weight bound. -/
theorem two_pow_pred_mul_classNumberOddPart_le_of_compatibility
    {hodd hplus k : ℕ} (hhplus : hplus ≠ 0)
    (hsame : hodd = (ordCompl[2] hplus : ℕ))
    (hgenus : 2 ^ (k - 1) ∣ hplus) :
    2 ^ (k - 1) * hodd ≤ hplus := by
  rw [hsame]
  have hpowproj : 2 ^ (k - 1) ∣ ordProj[2] hplus := by
    have h := Nat.ordProj_dvd_ordProj_of_dvd hhplus hgenus 2
    simpa only [Nat.ordProj_self_pow Nat.prime_two] using h
  have hle : 2 ^ (k - 1) ≤ ordProj[2] hplus :=
    Nat.le_of_dvd (Nat.ordProj_pos hplus 2) hpowproj
  exact (Nat.mul_le_mul_right (ordCompl[2] hplus) hle).trans_eq
    (Nat.ordProj_mul_ordCompl_eq_self hplus 2)

/-- Cast the natural genus inequality into the paper's real genus weight.
The positivity of `k` accounts explicitly for the predecessor exponent. -/
theorem classNumberOddPart_cast_le_two_mul_inverse_two_pow
    {hodd hplus k : ℕ} (hk : 0 < k)
    (hbound : 2 ^ (k - 1) * hodd ≤ hplus) :
    (hodd : ℝ) ≤
      2 * (1 / (2 : ℝ) ^ k) * (hplus : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.succ_sub_one] at hbound
  have hboundReal :
      (((2 ^ j) * hodd : ℕ) : ℝ) ≤ (hplus : ℝ) :=
    (Nat.cast_le (α := ℝ)).mpr hbound
  rw [show 2 * (1 / (2 : ℝ) ^ (j + 1)) * (hplus : ℝ) =
      (hplus : ℝ) / (2 : ℝ) ^ j by
    rw [pow_succ]
    field_simp]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j)).2
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hboundReal

/-- The source's pointwise inequality
`h_odd(K_D) <= 2 * w(D) * h^+(D)`, conditional only on the two exact
genus-theory interfaces named above. -/
theorem classNumberOddPart_cast_le_two_mul_genusWeight_mul_properFormClassCard
    (hcompat : ProperFormClassOddPartCompatibility)
    (hgenus : ProperFormClassGenusDivisibility)
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (positiveFundamentalDiscriminantOddClassNumber D : ℝ) ≤
      2 * genusWeight D * (Nat.card (ProperFormClass (D : ℤ)) : ℝ) := by
  unfold genusWeight
  apply classNumberOddPart_cast_le_two_mul_inverse_two_pow
    (ArithmeticFunction.cardDistinctFactors_pos.mpr hD.1)
  apply two_pow_pred_mul_classNumberOddPart_le_of_compatibility
    (properFormClass_card_pos_of_positiveFundamentalDiscriminant D hD).ne'
    (hcompat D hD)
    (hgenus D hD)

end

end PellPaper
