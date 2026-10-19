import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

/-!
# Relative primeness of integral polynomials after rational coefficient mapping

This Gauss-lemma adapter is the univariate step in the common-target-factor
route of the manuscript. It requires neither individual
primitivity nor nonzero hypotheses on the two polynomials. It does not
select or homogenize any factor.
-/

namespace PellPaper

noncomputable section
open Polynomial
open scoped nonZeroDivisors

/-- Relatively prime integral polynomials remain relatively prime over Q.
Individual contents need not be units, and either polynomial may be zero. -/
theorem isRelPrime_map_rat_of_isRelPrime_int (p q : Polynomial ℤ)
    (hpq : IsRelPrime p q) :
    IsRelPrime (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ)) := by
  intro d hdp hdq
  by_cases hd : d = 0
  · subst d
    have hp : p = 0 := (Polynomial.map_eq_zero_iff (Int.cast_injective)).mp
      (zero_dvd_iff.mp hdp)
    have hq : q = 0 := (Polynomial.map_eq_zero_iff (Int.cast_injective)).mp
      (zero_dvd_iff.mp hdq)
    subst p q
    exact False.elim ((hpq dvd_rfl dvd_rfl).ne_zero rfl)
  · let N : Polynomial ℤ := IsLocalization.integerNormalization ℤ⁰ d
    obtain ⟨c, hc, heq⟩ := IsLocalization.integerNormalization_spec ℤ⁰ d
    rw [Algebra.smul_def, Polynomial.algebraMap_apply] at heq
    change N.map (Int.castRingHom ℚ) = Polynomial.C (c : ℚ) * d at heq
    have hcQ : (c : ℚ) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.ne_zero hc
    have hunit : IsUnit (Polynomial.C (c : ℚ)) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcQ)
    have hdiv : N.primPart.map (Int.castRingHom ℚ) ∣ d := by
      apply hunit.dvd_mul_left.mp
      rw [← heq]
      exact map_dvd (Polynomial.mapRingHom (Int.castRingHom ℚ)) N.primPart_dvd
    have hNp : N.primPart ∣ p :=
      (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast N.primPart p
        N.isPrimitive_primPart).mpr (hdiv.trans hdp)
    have hNq : N.primPart ∣ q :=
      (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast N.primPart q
        N.isPrimitive_primPart).mpr (hdiv.trans hdq)
    exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart
      hd (hpq hNp hNq)

/-- Over the rational polynomial PID the mapped pair admits a Bezout identity.
No integral Bezout identity is assumed or asserted. -/
theorem isCoprime_map_rat_of_isRelPrime_int (p q : Polynomial ℤ)
    (hpq : IsRelPrime p q) :
    IsCoprime (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ)) :=
  (isRelPrime_map_rat_of_isRelPrime_int p q hpq).isCoprime

/-- Relatively prime integral polynomials have no common rational evaluation
root, including the cases of a zero component or constant components. -/
theorem eval_map_rat_ne_zero_or_ne_zero_of_isRelPrime_int
    (p q : Polynomial ℤ) (hpq : IsRelPrime p q) (x : ℚ) :
    (p.map (Int.castRingHom ℚ)).eval x ≠ 0 ∨
      (q.map (Int.castRingHom ℚ)).eval x ≠ 0 := by
  have h := (isCoprime_map_rat_of_isRelPrime_int p q hpq).map (Polynomial.evalRingHom x)
  change IsCoprime ((p.map (Int.castRingHom ℚ)).eval x)
    ((q.map (Int.castRingHom ℚ)).eval x) at h
  by_contra! hh
  rw [hh.1, hh.2] at h
  exact (h.isUnit_of_dvd' (dvd_refl 0) (dvd_refl 0)).ne_zero rfl

end
end PellPaper
