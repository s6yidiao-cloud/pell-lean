import Pell.CorollaryOddClassPointwise

/-!
# An ordinary-class genus input for Corollary 1.2

This module packages the weaker ordinary-class consequence of genus theory
needed by the odd class-number argument.  If
`2 ^ (omega(D) - 2)` divides the actual ordinary class number, then its odd
part is at most four times the genus weight times that class number.  The
proved wide-class comparison then supplies the existing downstream
`OddClassGenusPointwiseBound 4` interface.

The divisibility family is a named proposition, not an axiom.  In particular,
this file does not assert genus theory; it proves only the elementary
`ordCompl`, cast, and class-number comparison consequences of that input.
-/

namespace PellPaper

noncomputable section

open scoped ArithmeticFunction.omega
open IntegralBinaryQuadraticForm

/-- The exact ordinary-class divisibility input expected from genus theory.

For a real quadratic field the ordinary `2`-rank can be one smaller than the
narrow `2`-rank, which accounts for the predecessor by two rather than by one.
-/
def OrdinaryClassNumberGenusDivisibility : Prop :=
  ∀ (D : ℕ) (hD : PositiveFundamentalDiscriminant D),
    2 ^ (ω D - 2) ∣
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD

/-- The natural-number core: a guaranteed power of two in `h` can be removed
from `h` before its complementary odd factor is bounded. -/
theorem two_pow_sub_two_mul_ordCompl_two_le_of_dvd
    {h k : ℕ} (hh : h ≠ 0) (hdiv : 2 ^ (k - 2) ∣ h) :
    2 ^ (k - 2) * ordCompl[2] h ≤ h := by
  apply two_pow_pred_mul_classNumberOddPart_le_of_compatibility
    (k := k - 1) hh rfl
  simpa [Nat.sub_sub] using hdiv

/-- Real-valued form of the ordinary genus inequality.  The factor four is
exactly the cost of replacing `2 ^ (k - 2)` by the weight `2 ^ (-k)`.
-/
theorem ordCompl_two_cast_le_four_mul_inverse_two_pow_of_dvd
    {h k : ℕ} (hk : 0 < k) (hh : h ≠ 0) (hdiv : 2 ^ (k - 2) ∣ h) :
    ((ordCompl[2] h : ℕ) : ℝ) ≤ 4 * (1 / (2 : ℝ) ^ k) * (h : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  cases j with
  | zero =>
      have hodd : ordCompl[2] h ≤ h :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hh) (Nat.ordCompl_dvd h 2)
      have hoddReal : ((ordCompl[2] h : ℕ) : ℝ) ≤ (h : ℝ) := by
        exact_mod_cast hodd
      norm_num
      exact hoddReal.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) h])
  | succ j =>
      have hbound := two_pow_sub_two_mul_ordCompl_two_le_of_dvd hh hdiv
      have hboundNat : 2 ^ j * ordCompl[2] h ≤ h := by
        simpa using hbound
      have hboundReal :
          (((2 ^ j) * ordCompl[2] h : ℕ) : ℝ) ≤ (h : ℝ) := by
        exact_mod_cast hboundNat
      rw [show
        4 * (1 / (2 : ℝ) ^ (Nat.succ (Nat.succ j))) * (h : ℝ) =
            (h : ℝ) / (2 : ℝ) ^ j by
          rw [pow_succ, pow_succ]
          field_simp
          norm_num]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j)).2
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hboundReal

/-- Ordinary genus divisibility implies the exact genus interface already
consumed by the pointwise and finite-cutoff odd-class arguments.

The first inequality is against the actual ordinary class number; the last
step uses the proved surjection from proper form classes to wide ideal
classes. -/
theorem oddClassGenusPointwiseBound_four_of_ordinaryClassNumberGenusDivisibility
    (hgenus : OrdinaryClassNumberGenusDivisibility) :
    OddClassGenusPointwiseBound 4 := by
  refine ⟨by norm_num, ?_⟩
  intro D hD
  let h :=
    rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD
  have hh : h ≠ 0 :=
    (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD).ne'
  have hodd := ordCompl_two_cast_le_four_mul_inverse_two_pow_of_dvd
    (ArithmeticFunction.cardDistinctFactors_pos.mpr hD.1) hh (hgenus D hD)
  have hwide : (h : ℝ) ≤ (Nat.card (ProperFormClass (D : ℤ)) : ℝ) := by
    exact_mod_cast classNumber_le_properFormClass_card D hD
  rw [positiveFundamentalDiscriminantOddClassNumber_eq hD]
  unfold genusWeight
  exact hodd.trans (mul_le_mul_of_nonneg_left hwide (by positivity))

end

end PellPaper
