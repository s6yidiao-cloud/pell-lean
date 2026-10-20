import Pell.RealQuadraticFieldClassSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Order.Compact

/-!
# The odd class-number sum over real quadratic fields

This module fixes the statement layer for `T:odd-class-average` of
`paper/main.tex`. The summand is Mathlib's `ordCompl[2]`, the complementary
factor to the full power of two in the actual ordinary ideal class number.
Thus no surrogate odd-part function or class-number model enters the
headline assertion.

The finite field sum is proved equal to a discriminant-indexed sum only
after applying the existing equivalence between actual real quadratic field
isomorphism classes and positive fundamental discriminants.  The final
section records elementary positivity, monotonicity, and compact-range
completion facts.  It contains no genus-theory or analytic estimate.
-/

namespace PellPaper

open Filter Set
open scoped BigOperators

noncomputable section

/-! ## Largest odd divisors -/

/-- For a nonzero natural number, `ordCompl[2] n` is its largest odd divisor.

The maximality conclusion is stated in the divisibility order, which is
stronger than the corresponding numerical inequality on natural numbers. -/
theorem ordCompl_two_isLargestOddDivisor (n : ℕ) (hn : n ≠ 0) :
    ordCompl[2] n ∣ n ∧ Odd (ordCompl[2] n) ∧
      ∀ d : ℕ, d ∣ n → Odd d → d ∣ ordCompl[2] n := by
  refine ⟨Nat.ordCompl_dvd n 2, ?_, ?_⟩
  · apply Nat.not_even_iff_odd.mp
    intro heven
    exact Nat.not_dvd_ordCompl Nat.prime_two hn (even_iff_two_dvd.mp heven)
  · intro d hdn hodd
    apply Nat.dvd_ordCompl_of_dvd_not_dvd hdn
    intro htwo
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr htwo)

/-- The numerical maximality form of `ordCompl_two_isLargestOddDivisor`. -/
theorem le_ordCompl_two_of_dvd_of_odd {d n : ℕ} (hn : n ≠ 0)
    (hdn : d ∣ n) (hodd : Odd d) :
    d ≤ ordCompl[2] n := by
  exact Nat.le_of_dvd (Nat.ordCompl_pos 2 hn)
    ((ordCompl_two_isLargestOddDivisor n hn).2.2 d hdn hodd)

/-! ## Actual field and discriminant-indexed summands -/

/-- The largest odd divisor of the actual ordinary ideal class number of a
real quadratic field isomorphism class. -/
def realQuadraticFieldOddClassNumber (K : RealQuadraticFieldClass) : ℕ :=
  ordCompl[2] (realQuadraticFieldClassNumber K)

/-- Every actual real quadratic field class has positive ordinary class
number. -/
theorem realQuadraticFieldClassNumber_pos (K : RealQuadraticFieldClass) :
    0 < realQuadraticFieldClassNumber K := by
  obtain ⟨D, rfl⟩ := positiveFundamentalToRealQuadraticFieldClass_surjective K
  rw [realQuadraticFieldClassNumber_positiveFundamental]
  exact rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos
    D.val D.property

/-- The actual odd class number divides the actual ordinary class number. -/
theorem realQuadraticFieldOddClassNumber_dvd (K : RealQuadraticFieldClass) :
    realQuadraticFieldOddClassNumber K ∣ realQuadraticFieldClassNumber K := by
  exact Nat.ordCompl_dvd _ 2

/-- The actual odd class number is odd. -/
theorem realQuadraticFieldOddClassNumber_odd (K : RealQuadraticFieldClass) :
    Odd (realQuadraticFieldOddClassNumber K) := by
  exact (ordCompl_two_isLargestOddDivisor _
    (realQuadraticFieldClassNumber_pos K).ne').2.1

/-- The actual odd class number is positive. -/
theorem realQuadraticFieldOddClassNumber_pos (K : RealQuadraticFieldClass) :
    0 < realQuadraticFieldOddClassNumber K := by
  exact Nat.ordCompl_pos 2 (realQuadraticFieldClassNumber_pos K).ne'

/-- Any odd divisor of the ordinary class number divides the named odd class
number. -/
theorem dvd_realQuadraticFieldOddClassNumber_of_dvd_of_odd
    (K : RealQuadraticFieldClass) {d : ℕ}
    (hd : d ∣ realQuadraticFieldClassNumber K) (hodd : Odd d) :
    d ∣ realQuadraticFieldOddClassNumber K := by
  exact (ordCompl_two_isLargestOddDivisor _
    (realQuadraticFieldClassNumber_pos K).ne').2.2 d hd hodd

/-- Consequently, the named quantity is numerically the largest odd divisor
of the ordinary class number. -/
theorem le_realQuadraticFieldOddClassNumber_of_dvd_of_odd
    (K : RealQuadraticFieldClass) {d : ℕ}
    (hd : d ∣ realQuadraticFieldClassNumber K) (hodd : Odd d) :
    d ≤ realQuadraticFieldOddClassNumber K := by
  exact Nat.le_of_dvd (realQuadraticFieldOddClassNumber_pos K)
    (dvd_realQuadraticFieldOddClassNumber_of_dvd_of_odd K hd hodd)

/-- A total discriminant-indexed odd class number.  At positive fundamental
discriminants it is the odd part of the actual class number of the concrete
quadratic field; values away from that locus are irrelevant to all sums in
this module. -/
def positiveFundamentalDiscriminantOddClassNumber (D : ℕ) : ℕ :=
  ordCompl[2] (genuineQuadraticAlgebraClassNumberModel.ordinaryClassNumber D)

/-- On the positive-fundamental locus, the total discriminant-indexed
definition is literally the odd part of the corresponding concrete field's
actual class number. -/
theorem positiveFundamentalDiscriminantOddClassNumber_eq
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    positiveFundamentalDiscriminantOddClassNumber D =
      ordCompl[2]
        (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD) := by
  unfold positiveFundamentalDiscriminantOddClassNumber
  rw [genuineQuadraticAlgebraClassNumberModel_ordinary_eq hD]

/-- The discriminant-indexed odd class number is positive on the
positive-fundamental locus. -/
theorem positiveFundamentalDiscriminantOddClassNumber_pos
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    0 < positiveFundamentalDiscriminantOddClassNumber D := by
  rw [positiveFundamentalDiscriminantOddClassNumber_eq hD]
  exact Nat.ordCompl_pos 2
    (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD).ne'

/-- Pointwise form of the field/discriminant transport used by the sum
identity below. -/
theorem realQuadraticFieldOddClassNumber_positiveFundamental
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) :
    realQuadraticFieldOddClassNumber
        (positiveFundamentalToRealQuadraticFieldClass D) =
      positiveFundamentalDiscriminantOddClassNumber D.val := by
  unfold realQuadraticFieldOddClassNumber
  rw [realQuadraticFieldClassNumber_positiveFundamental,
    positiveFundamentalDiscriminantOddClassNumber_eq D.property]

/-- The discriminant-indexed odd class number is odd on the
positive-fundamental locus. -/
theorem positiveFundamentalDiscriminantOddClassNumber_odd
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    Odd (positiveFundamentalDiscriminantOddClassNumber D) := by
  rw [positiveFundamentalDiscriminantOddClassNumber_eq hD]
  exact (ordCompl_two_isLargestOddDivisor _
    (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos
      D hD).ne').2.1

/-- The discriminant-indexed odd class number divides the actual ordinary
class number on the positive-fundamental locus. -/
theorem positiveFundamentalDiscriminantOddClassNumber_dvd
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    positiveFundamentalDiscriminantOddClassNumber D ∣
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  rw [positiveFundamentalDiscriminantOddClassNumber_eq hD]
  exact Nat.ordCompl_dvd _ 2

/-- Numerical comparison with the full ordinary class number. -/
theorem positiveFundamentalDiscriminantOddClassNumber_le
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    positiveFundamentalDiscriminantOddClassNumber D ≤
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  exact Nat.le_of_dvd
    (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD)
    (positiveFundamentalDiscriminantOddClassNumber_dvd hD)

/-- The finite sum of actual odd class numbers, with each real quadratic
field isomorphism class represented exactly once and cutoff `0 < D_K < X`. -/
def realQuadraticFieldOddClassSum (X : ℝ) : ℝ :=
  ∑ K ∈ realQuadraticFieldClassesBelow X,
    (realQuadraticFieldOddClassNumber K : ℝ)

/-- The corresponding finite sum indexed by positive fundamental
discriminants with the same strict real cutoff. -/
def positiveFundamentalDiscriminantOddClassSum (X : ℝ) : ℝ :=
  ∑ D ∈ fundamentalDiscriminantsBelow X,
    (positiveFundamentalDiscriminantOddClassNumber D : ℝ)

/-- Exact transport from the literal field-isomorphism-class sum to the
positive-fundamental-discriminant sum.  This is a theorem using the proved
field classification, not a definitional replacement of the source sum. -/
theorem realQuadraticFieldOddClassSum_eq_positiveFundamentalDiscriminantOddClassSum
    (X : ℝ) :
    realQuadraticFieldOddClassSum X =
      positiveFundamentalDiscriminantOddClassSum X := by
  classical
  unfold realQuadraticFieldOddClassSum realQuadraticFieldClassesBelow
  rw [Finset.sum_map]
  calc
    (∑ D ∈ (fundamentalDiscriminantsBelow X).subtype PositiveFundamentalDiscriminant,
        (realQuadraticFieldOddClassNumber (positiveFundamentalFieldClassEquiv D) : ℝ)) =
      ∑ D ∈ (fundamentalDiscriminantsBelow X).subtype PositiveFundamentalDiscriminant,
        (positiveFundamentalDiscriminantOddClassNumber D.val : ℝ) := by
      apply Finset.sum_congr rfl
      intro D _hD
      exact_mod_cast realQuadraticFieldOddClassNumber_positiveFundamental D
    _ = positiveFundamentalDiscriminantOddClassSum X := by
      unfold positiveFundamentalDiscriminantOddClassSum
      exact Finset.sum_subtype_of_mem
        (fun D : ℕ ↦ (positiveFundamentalDiscriminantOddClassNumber D : ℝ))
        (fun D hD ↦ (mem_fundamentalDiscriminantsBelow.mp hD).1)

/-! ## Elementary order properties -/

theorem realQuadraticFieldOddClassSum_nonneg (X : ℝ) :
    0 ≤ realQuadraticFieldOddClassSum X := by
  unfold realQuadraticFieldOddClassSum
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

theorem positiveFundamentalDiscriminantOddClassSum_nonneg (X : ℝ) :
    0 ≤ positiveFundamentalDiscriminantOddClassSum X := by
  unfold positiveFundamentalDiscriminantOddClassSum
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

theorem realQuadraticFieldClassesBelow_mono {X Y : ℝ} (hXY : X ≤ Y) :
    realQuadraticFieldClassesBelow X ⊆ realQuadraticFieldClassesBelow Y := by
  intro K hK
  rw [mem_realQuadraticFieldClassesBelow] at hK ⊢
  exact hK.trans_le hXY

theorem realQuadraticFieldOddClassSum_mono {X Y : ℝ} (hXY : X ≤ Y) :
    realQuadraticFieldOddClassSum X ≤ realQuadraticFieldOddClassSum Y := by
  unfold realQuadraticFieldOddClassSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (realQuadraticFieldClassesBelow_mono hXY)
  intro K _ _
  exact Nat.cast_nonneg _

theorem positiveFundamentalDiscriminantOddClassSum_mono {X Y : ℝ} (hXY : X ≤ Y) :
    positiveFundamentalDiscriminantOddClassSum X ≤
      positiveFundamentalDiscriminantOddClassSum Y := by
  unfold positiveFundamentalDiscriminantOddClassSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (fundamentalDiscriminantsBelow_mono hXY)
  intro D _ _
  exact Nat.cast_nonneg _

/-! ## Exact Corollary 1.2 scale and assertion -/

/-- The exact real-valued scale in Corollary 1.2:
`X^(3/2) * sqrt(log(log X)) / (log X)^2`. -/
def oddClassAverageScale (X : ℝ) : ℝ :=
  Real.rpow X (3 / 2) * Real.sqrt (Real.log (Real.log X)) /
    (Real.log X) ^ 2

theorem oddClassAverageScale_nonneg {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ oddClassAverageScale X := by
  unfold oddClassAverageScale
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hX) _)
      (Real.sqrt_nonneg _))
    (sq_nonneg _)

theorem oddClassAverageScale_pos_of_three_le {X : ℝ} (hX : 3 ≤ X) :
    0 < oddClassAverageScale X := by
  have hExpX : Real.exp 1 < X := Real.exp_one_lt_three.trans_le hX
  have hlogOne : 1 < Real.log X :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr hExpX
  have hlogLog : 0 < Real.log (Real.log X) := Real.log_pos hlogOne
  unfold oddClassAverageScale
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (Real.sqrt_pos.2 hlogLog))
    (sq_pos_of_pos (zero_lt_one.trans hlogOne))

/-- Formal target corresponding to `T:odd-class-average` of `paper/main.tex`.

One positive implied constant is chosen before the real cutoff `X`; the sum
is over actual real quadratic field isomorphism classes satisfying the
strict actual-discriminant condition `0 < D_K < X`. -/
def RealQuadraticFieldOddClassAverageAssertion : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    realQuadraticFieldOddClassSum X ≤ C * oddClassAverageScale X

/-! ## Compact completion of an eventual estimate -/

theorem continuousOn_oddClassAverageScale_Icc (T : ℝ) :
    ContinuousOn oddClassAverageScale (Icc (3 : ℝ) T) := by
  have hlog : ContinuousOn (fun X : ℝ ↦ Real.log X) (Icc (3 : ℝ) T) :=
    Real.continuousOn_log.mono fun X hX ↦ ne_of_gt (by linarith [hX.1])
  have hlogLog : ContinuousOn (fun X : ℝ ↦ Real.log (Real.log X))
      (Icc (3 : ℝ) T) :=
    Real.continuousOn_log.comp' hlog (fun X hX ↦
      ne_of_gt (Real.log_pos (by linarith [hX.1])))
  have hXpow : ContinuousOn (fun X : ℝ ↦ Real.rpow X (3 / 2))
      (Icc (3 : ℝ) T) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  have hsqrtLogLog : ContinuousOn
      (fun X : ℝ ↦ Real.sqrt (Real.log (Real.log X))) (Icc (3 : ℝ) T) :=
    Real.continuous_sqrt.comp_continuousOn' hlogLog
  have hlogSq : ContinuousOn (fun X : ℝ ↦ (Real.log X) ^ 2)
      (Icc (3 : ℝ) T) :=
    hlog.pow 2
  have hdenom : ∀ X ∈ Icc (3 : ℝ) T, (Real.log X) ^ 2 ≠ 0 := by
    intro X hX
    exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [hX.1])))
  change ContinuousOn
    (fun X : ℝ ↦ Real.rpow X (3 / 2) * Real.sqrt (Real.log (Real.log X)) /
      (Real.log X) ^ 2)
    (Icc (3 : ℝ) T)
  exact (hXpow.mul hsqrtLogLog).div hlogSq hdenom

/-- On each fixed cutoff interval relevant to the corollary, the target
scale admits one strictly positive lower bound. -/
theorem exists_pos_le_oddClassAverageScale_Icc (T : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ X ∈ Icc (3 : ℝ) T,
      b ≤ oddClassAverageScale X := by
  exact isCompact_Icc.exists_forall_le'
    (continuousOn_oddClassAverageScale_Icc T)
    (fun X hX ↦ oddClassAverageScale_pos_of_three_le hX.1)

/-- The actual odd class-number sum has a uniform multiple of the target
scale on every fixed finite cutoff interval. -/
theorem exists_realQuadraticFieldOddClassSum_compactRange_bound (T : ℝ) :
    ∃ Bsmall : ℝ, 0 ≤ Bsmall ∧ ∀ X : ℝ, 3 ≤ X → X ≤ T →
      realQuadraticFieldOddClassSum X ≤ Bsmall * oddClassAverageScale X := by
  obtain ⟨b, hb, hscale⟩ := exists_pos_le_oddClassAverageScale_Icc T
  refine ⟨realQuadraticFieldOddClassSum T / b,
    div_nonneg (realQuadraticFieldOddClassSum_nonneg _) hb.le, ?_⟩
  intro X hXthree hXupper
  have hsum : realQuadraticFieldOddClassSum X ≤ realQuadraticFieldOddClassSum T :=
    realQuadraticFieldOddClassSum_mono hXupper
  have hscaleX : b ≤ oddClassAverageScale X := hscale X ⟨hXthree, hXupper⟩
  have hquotient_nonneg : 0 ≤ realQuadraticFieldOddClassSum T / b :=
    div_nonneg (realQuadraticFieldOddClassSum_nonneg _) hb.le
  calc
    realQuadraticFieldOddClassSum X ≤ realQuadraticFieldOddClassSum T := hsum
    _ = (realQuadraticFieldOddClassSum T / b) * b := by
      rw [div_mul_cancel₀ _ hb.ne']
    _ ≤ (realQuadraticFieldOddClassSum T / b) * oddClassAverageScale X :=
      mul_le_mul_of_nonneg_left hscaleX hquotient_nonneg

/-- Any eventual estimate with the exact Corollary 1.2 scale extends to the
source's complete range `X ≥ 3`, without an additional arithmetic premise for
bounded cutoffs. -/
theorem realQuadraticFieldOddClassAverageAssertion_of_eventually_bound
    (K : ℝ)
    (hlarge : ∀ᶠ X : ℝ in atTop,
      realQuadraticFieldOddClassSum X ≤ K * oddClassAverageScale X) :
    RealQuadraticFieldOddClassAverageAssertion := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hlarge
  let U : ℝ := max T 3
  obtain ⟨Bsmall, hBsmall, hsmall⟩ :=
    exists_realQuadraticFieldOddClassSum_compactRange_bound U
  let C : ℝ := |K| + Bsmall + 1
  have hC : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg K, hBsmall]
  refine ⟨C, hC, ?_⟩
  intro X hXthree
  by_cases hlargeX : U ≤ X
  · have hscale : 0 ≤ oddClassAverageScale X :=
      (oddClassAverageScale_pos_of_three_le hXthree).le
    calc
      realQuadraticFieldOddClassSum X ≤ K * oddClassAverageScale X :=
        hT X ((le_max_left T 3).trans hlargeX)
      _ ≤ C * oddClassAverageScale X := by
        apply mul_le_mul_of_nonneg_right _ hscale
        dsimp [C]
        nlinarith [le_abs_self K, hBsmall]
  · have hXupper : X ≤ U := le_of_not_ge hlargeX
    have hscale : 0 ≤ oddClassAverageScale X :=
      (oddClassAverageScale_pos_of_three_le hXthree).le
    calc
      realQuadraticFieldOddClassSum X ≤ Bsmall * oddClassAverageScale X :=
        hsmall X hXthree hXupper
      _ ≤ C * oddClassAverageScale X := by
        apply mul_le_mul_of_nonneg_right _ hscale
        dsimp [C]
        nlinarith [abs_nonneg K]

end

end PellPaper
