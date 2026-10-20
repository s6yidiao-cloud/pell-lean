import Pell.ClassRegulatorReparam
import Pell.Elementary
import Pell.FundamentalDiscriminantPellBridge

/-!
# The logarithmic bridge from quadratic units to Pell cutoffs

For a positive fundamental discriminant `D`, a fundamental Pell solution has
an actual positive real value `epsilon a`.  This file defines its normalized
logarithm and proves the elementary implication used in the class-number
argument: an upper comparison `epsilon a ≤ eta ^ 6`, together with a cutoff
on `log eta / log D`, gives the Pell exceptional-set condition at
`6 * max (1 / 2) t`.

Thus the remaining field-theoretic input is precisely the comparison between
the fundamental unit of the maximal order and the Pell solution.  No such
comparison, class-number formula, or Dirichlet `L`-function estimate is
assumed or asserted here.
-/

namespace PellPaper

noncomputable section

/-- The normalized logarithmic size of a Pell solution at a natural radicand.
On positive fundamental discriminants, the denominator is positive. -/
def pellNormalizedLog {D : ℕ} (a : Pell.Solution₁ (D : ℤ)) : ℝ :=
  Real.log (epsilon a) / Real.log (D : ℝ)

/-- A fundamental Pell solution at a positive fundamental discriminant has a
strictly positive real value. -/
theorem epsilon_pos_of_isFundamental_of_positiveFundamentalDiscriminant
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a) :
    0 < epsilon a := by
  have hDpos : 0 < (D : ℤ) := int_pos_of_positiveFundamentalDiscriminant hD
  have hsqrt : 0 < Real.sqrt ((D : ℤ) : ℝ) := by
    rw [Real.sqrt_pos]
    exact_mod_cast hDpos
  exact hsqrt.trans (sqrt_lt_epsilon ha)

/-- On a positive fundamental discriminant, the definition of a small
fundamental solution is exactly a normalized-logarithm cutoff for the unique
fundamental Pell solution. -/
theorem smallFundamentalSolution_iff_pellNormalizedLog_le
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a) (theta : ℝ) :
    SmallFundamentalSolution theta D ↔ pellNormalizedLog a ≤ theta := by
  have hDone : 1 < D := hD.1
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast hDone
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hDreal
  have heps : 0 < epsilon a :=
    epsilon_pos_of_isFundamental_of_positiveFundamentalDiscriminant hD ha
  rw [smallFundamentalSolution_iff_of_isFundamental ha]
  constructor
  · intro hsmall
    exact (div_le_iff₀ hlogD).mpr
      ((Real.le_rpow_iff_log_le heps (by positivity)).mp hsmall)
  · intro hlog
    exact (Real.le_rpow_iff_log_le heps (by positivity)).mpr
      ((div_le_iff₀ hlogD).mp hlog)

/-- The upper half of the unit comparison `epsilon ≤ eta ^ 6` bounds the
normalized Pell logarithm by six times the normalized logarithm of `eta`. -/
theorem pellNormalizedLog_le_six_mul_log_div_of_epsilon_le_pow_six
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a)
    {eta : ℝ} (heta : 0 < eta) (hcomparison : epsilon a ≤ eta ^ 6) :
    pellNormalizedLog a ≤ 6 * (Real.log eta / Real.log (D : ℝ)) := by
  have hDone : 1 < D := hD.1
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast hDone
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hDreal
  have heps : 0 < epsilon a :=
    epsilon_pos_of_isFundamental_of_positiveFundamentalDiscriminant hD ha
  have hlog : Real.log (epsilon a) ≤ (6 : ℝ) * Real.log eta := by
    have h := Real.log_le_log heps hcomparison
    rw [← Real.rpow_natCast, Real.log_rpow heta] at h
    norm_num at h ⊢
    exact h
  unfold pellNormalizedLog
  calc
    Real.log (epsilon a) / Real.log (D : ℝ) ≤
        ((6 : ℝ) * Real.log eta) / Real.log (D : ℝ) :=
      div_le_div_of_nonneg_right hlog hlogD.le
    _ = 6 * (Real.log eta / Real.log (D : ℝ)) := by ring

/-- The exact field-to-Pell cutoff conversion used in the class-number
argument.  Once a positive real `eta` satisfies the upper unit comparison,
the strict normalized regulator cutoff produces a genuine member of the
Pell exceptional family at the reparameterized exponent. -/
theorem smallFundamentalSolution_regulatorPellExponent_of_unitComparison
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a)
    {eta t : ℝ} (heta : 0 < eta) (hcomparison : epsilon a ≤ eta ^ 6)
    (hcutoff : Real.log eta / Real.log (D : ℝ) < t) :
    SmallFundamentalSolution (regulatorPellExponent t) D := by
  rw [smallFundamentalSolution_iff_pellNormalizedLog_le hD ha]
  calc
    pellNormalizedLog a ≤ 6 * (Real.log eta / Real.log (D : ℝ)) :=
      pellNormalizedLog_le_six_mul_log_div_of_epsilon_le_pow_six hD ha heta hcomparison
    _ ≤ 6 * t := by nlinarith
    _ ≤ regulatorPellExponent t := by
      unfold regulatorPellExponent
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

end

end PellPaper
