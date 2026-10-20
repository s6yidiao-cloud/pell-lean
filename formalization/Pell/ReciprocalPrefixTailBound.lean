import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.AbelSummation

/-!
# A finite reciprocal tail from bounded actual prefixes

Modified adaptation of FormalPantheon, commit
`ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`, file
`BoundedGaps/BoundedGaps/BombieriVinogradov/Analytic/CharacterPartialSummation.lean`.
Upstream: https://github.com/frenzymath/FormalPantheon
Apache-2.0; full license: `third_party/FormalPantheon-LICENSE`.

Changes: only the reciprocal-tail argument is retained; the character is
generalized to a complex sequence vanishing at zero, and the external PV
bound is replaced by an explicit bound `B` on its actual prefixes. No upstream
module is imported. The resulting bound is `2 * B / x`, including empty tails.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PellPaper

private lemma hasDerivAt_complexOfReal_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹))
      (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) :=
    hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma integrableOn_deriv_complexOfReal_inv
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (hasDerivAt_complexOfReal_inv (ha.trans_le ht.1).ne').deriv.symm

private lemma integral_Ioc_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

/-- Uniformly bounded natural prefixes give a finite reciprocal-tail bound.
The finite interval is exactly `(x,y]`, with `x > 0`; no order assumption on
`y` is needed. -/
theorem norm_reciprocal_sum_Ioc_le_of_prefixBound
    (c : ℕ → ℂ) (hc0 : c 0 = 0) (B : ℝ)
    (hprefix : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, c n‖ ≤ B)
    (x y : ℕ) (hx : 0 < x) :
    ‖∑ n ∈ Finset.Ioc x y, c n / (n : ℂ)‖ ≤ 2 * B / (x : ℝ) := by
  have hB : 0 ≤ B := by simpa using hprefix 0
  let A : ℝ → ℂ := fun t ↦ ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n
  have hA (t : ℝ) : ‖A t‖ ≤ B := by
    dsimp only [A]
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons,
      hc0, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊]
    simpa using hprefix ⌊t⌋₊
  by_cases hxy : x ≤ y
  · have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hyReal : 0 < (y : ℝ) := hxReal.trans_le hxyReal
    have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
      intro t ht
      exact (hasDerivAt_complexOfReal_inv
        (hxReal.trans_le ht.1).ne').differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
      integrableOn_deriv_complexOfReal_inv hxReal
    have habel := sum_mul_eq_sub_sub_integral_mul'
      (f := fun t : ℝ ↦ ((t : ℂ)⁻¹)) (c := c) hxy hfDiff hfInt
    have hrepresentation :
        (∑ n ∈ Finset.Ioc x y, c n / (n : ℂ)) =
          ((y : ℂ)⁻¹ * A y - (x : ℂ)⁻¹ * A x) -
            ∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t := by
      simpa [A, div_eq_mul_inv, mul_comm] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t)
        (Ioc (x : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc c hxReal.le hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hReciprocalContinuous : ContinuousOn
        (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.pow 2
      · intro t ht
        exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
    have hMajorant : IntegrableOn
        (fun t : ℝ ↦ B * (t ^ 2)⁻¹) (Ioc (x : ℝ) y) :=
      (continuousOn_const.mul hReciprocalContinuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
        ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤ B * (t ^ 2)⁻¹ := by
      intro t ht
      have htPos : 0 < t := hxReal.trans ht.1
      rw [(hasDerivAt_complexOfReal_inv htPos.ne').deriv, norm_mul]
      have hderivNorm : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
        rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htPos]
      rw [hderivNorm]
      calc
        (t ^ 2)⁻¹ * ‖A t‖ = ‖A t‖ * (t ^ 2)⁻¹ := mul_comm _ _
        _ ≤ B * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (hA t)
          (inv_nonneg.mpr (sq_nonneg t))
    have hIntegral :
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
          B * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      calc
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
            ∫ t in Ioc (x : ℝ) y,
              ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioc (x : ℝ) y, B * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = B * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
          rw [integral_const_mul, integral_Ioc_inv_sq hxReal hxyReal]
    have hUpper : ‖(y : ℂ)⁻¹ * A y‖ ≤ B * (y : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (y : ℝ)⁻¹ * ‖A y‖ ≤ (y : ℝ)⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hA y) (inv_nonneg.mpr hyReal.le)
        _ = B * (y : ℝ)⁻¹ := mul_comm _ _
    have hLower : ‖(x : ℂ)⁻¹ * A x‖ ≤ B * (x : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (x : ℝ)⁻¹ * ‖A x‖ ≤ (x : ℝ)⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hA x) (inv_nonneg.mpr hxReal.le)
        _ = B * (x : ℝ)⁻¹ := mul_comm _ _
    rw [hrepresentation]
    calc
      ‖((y : ℂ)⁻¹ * A y - (x : ℂ)⁻¹ * A x) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ ≤
          (‖(y : ℂ)⁻¹ * A y‖ + ‖(x : ℂ)⁻¹ * A x‖) +
            ‖∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t * A t‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (B * (y : ℝ)⁻¹ + B * (x : ℝ)⁻¹) +
          B * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) :=
        add_le_add (add_le_add hUpper hLower) hIntegral
      _ = 2 * B / (x : ℝ) := by ring
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Finset.Ioc_eq_empty_of_le hyx, Finset.sum_empty, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hB) (by positivity)

end PellPaper
