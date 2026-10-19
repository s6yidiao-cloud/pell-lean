import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Primorial
import Pell.SquarePartTailAnalytic
import Pell.WilsonNeutralizerTotalMassExpansion
import Pell.WilsonSelbergCoefficientMass
import Pell.WilsonSelbergShortUpperWeights

/-!
# The half-dimensional Selberg mass for Wilson's divisor weight

This file isolates the lower bound for the Selberg bounding sum associated to
the local density `nu(p) = 1 / (2p)`.  The proof is finite: the square of the
truncated sum dominates the reciprocal harmonic mass of the squarefree
integers, while square-part decomposition shows that this mass is at least a
fixed proportion of the ordinary harmonic sum.
-/

namespace PellPaper

open scoped BigOperators ArithmeticFunction.Moebius

open Finset Nat ArithmeticFunction

noncomputable section

/-- The multiplicative half-dimensional local density.  Only its values on
squarefree integers are used by the Selberg sieve. -/
def main4WilsonHalfDensity : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p ↦ (2 * (p : ℝ))⁻¹

@[simp]
theorem main4WilsonHalfDensity_apply_prime {p : ℕ} (hp : p.Prime) :
    main4WilsonHalfDensity p = (2 * (p : ℝ))⁻¹ := by
  simp [main4WilsonHalfDensity, ArithmeticFunction.prodPrimeFactors_apply,
    hp.ne_zero, hp.primeFactors]

theorem main4WilsonHalfDensity_isMultiplicative :
    main4WilsonHalfDensity.IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

/-- A chosen squarefree kernel of a natural number. -/
def main4WilsonSquarefreeKernel (n : ℕ) : ℕ :=
  Classical.choose (Nat.sq_mul_squarefree n)

/-- A chosen square-part root paired with `main4WilsonSquarefreeKernel`. -/
def main4WilsonSquarePartRoot (n : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Nat.sq_mul_squarefree n))

theorem main4WilsonSquarePartRoot_sq_mul_squarefreeKernel (n : ℕ) :
    main4WilsonSquarePartRoot n ^ 2 * main4WilsonSquarefreeKernel n = n :=
  (Classical.choose_spec
    (Classical.choose_spec (Nat.sq_mul_squarefree n))).1

theorem main4WilsonSquarefreeKernel_squarefree (n : ℕ) :
    Squarefree (main4WilsonSquarefreeKernel n) :=
  (Classical.choose_spec
    (Classical.choose_spec (Nat.sq_mul_squarefree n))).2

/-- Reciprocal harmonic mass restricted to positive squarefree integers. -/
def main4WilsonSquarefreeHarmonicMass (R : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 R).filter Squarefree, 1 / (n : ℝ)

private def main4WilsonSquareDecomposition (n : ℕ) : ℕ × ℕ :=
  (main4WilsonSquarePartRoot n, main4WilsonSquarefreeKernel n)

private def main4WilsonSquareDecompositionWeight (x : ℕ × ℕ) : ℝ :=
  (1 / (x.1 : ℝ) ^ 2) * (1 / (x.2 : ℝ))

private theorem main4WilsonSquareDecomposition_injective_on (R : ℕ) :
    Set.InjOn main4WilsonSquareDecomposition (Finset.Ioc 0 R) := by
  intro m _hm n _hn hmn
  have hroot : main4WilsonSquarePartRoot m =
      main4WilsonSquarePartRoot n := congrArg Prod.fst hmn
  have hkernel : main4WilsonSquarefreeKernel m =
      main4WilsonSquarefreeKernel n := congrArg Prod.snd hmn
  rw [← main4WilsonSquarePartRoot_sq_mul_squarefreeKernel m,
    ← main4WilsonSquarePartRoot_sq_mul_squarefreeKernel n,
    hroot, hkernel]

private theorem main4WilsonSquareDecomposition_mem_product
    {R n : ℕ} (hn : n ∈ Finset.Ioc 0 R) :
    main4WilsonSquareDecomposition n ∈
      Finset.Ioc 0 R ×ˢ
        (Finset.Ioc 0 R).filter Squarefree := by
  have hnPos : 0 < n := (Finset.mem_Ioc.mp hn).1
  have hnR : n ≤ R := (Finset.mem_Ioc.mp hn).2
  have hdecomp := main4WilsonSquarePartRoot_sq_mul_squarefreeKernel n
  have hmulPos : 0 < main4WilsonSquarePartRoot n ^ 2 *
      main4WilsonSquarefreeKernel n := hdecomp.symm ▸ hnPos
  obtain ⟨hrootSqPos, hkernelPos⟩ :=
    CanonicallyOrderedAdd.mul_pos.mp hmulPos
  have hrootPos : 0 < main4WilsonSquarePartRoot n :=
    (pow_pos_iff (by norm_num : 2 ≠ 0)).mp hrootSqPos
  have hrootDvd : main4WilsonSquarePartRoot n ∣ n := by
    refine ⟨main4WilsonSquarePartRoot n * main4WilsonSquarefreeKernel n, ?_⟩
    calc
      n = main4WilsonSquarePartRoot n ^ 2 *
            main4WilsonSquarefreeKernel n := hdecomp.symm
      _ = main4WilsonSquarePartRoot n *
          (main4WilsonSquarePartRoot n * main4WilsonSquarefreeKernel n) := by ring
  have hkernelDvd : main4WilsonSquarefreeKernel n ∣ n := by
    refine ⟨main4WilsonSquarePartRoot n ^ 2, ?_⟩
    calc
      n = main4WilsonSquarePartRoot n ^ 2 *
          main4WilsonSquarefreeKernel n := hdecomp.symm
      _ = main4WilsonSquarefreeKernel n *
          main4WilsonSquarePartRoot n ^ 2 := by ring
  simp only [main4WilsonSquareDecomposition, Finset.mem_product,
    Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hrootPos, (Nat.le_of_dvd hnPos hrootDvd).trans hnR⟩,
    ⟨⟨hkernelPos, (Nat.le_of_dvd hnPos hkernelDvd).trans hnR⟩,
      main4WilsonSquarefreeKernel_squarefree n⟩⟩

private theorem main4WilsonSquareDecompositionWeight_apply (n : ℕ)
    (hn : 0 < n) :
    main4WilsonSquareDecompositionWeight
        (main4WilsonSquareDecomposition n) = 1 / (n : ℝ) := by
  have hdecomp := main4WilsonSquarePartRoot_sq_mul_squarefreeKernel n
  have hrootPos : 0 < main4WilsonSquarePartRoot n := by
    have hmulPos : 0 < main4WilsonSquarePartRoot n ^ 2 *
        main4WilsonSquarefreeKernel n := hdecomp.symm ▸ hn
    exact (pow_pos_iff (by norm_num : 2 ≠ 0)).mp
      (CanonicallyOrderedAdd.mul_pos.mp hmulPos).1
  have hkernelPos : 0 < main4WilsonSquarefreeKernel n := by
    have hmulPos : 0 < main4WilsonSquarePartRoot n ^ 2 *
        main4WilsonSquarefreeKernel n := hdecomp.symm ▸ hn
    exact (CanonicallyOrderedAdd.mul_pos.mp hmulPos).2
  have hcast : (n : ℝ) =
      (main4WilsonSquarePartRoot n : ℝ) ^ 2 *
        (main4WilsonSquarefreeKernel n : ℝ) := by
    exact_mod_cast hdecomp.symm
  unfold main4WilsonSquareDecompositionWeight main4WilsonSquareDecomposition
  rw [hcast]
  field_simp

/-- Square-part decomposition loses at most the convergent reciprocal-square
factor `2`: the squarefree reciprocal mass is at least half of the ordinary
harmonic sum. -/
theorem harmonic_le_two_mul_main4WilsonSquarefreeHarmonicMass (R : ℕ) :
    (harmonic R : ℝ) ≤ 2 * main4WilsonSquarefreeHarmonicMass R := by
  let source : Finset ℕ := Finset.Ioc 0 R
  let target : Finset (ℕ × ℕ) :=
    source ×ˢ source.filter Squarefree
  have hsource : source = Finset.Ioc 0 R := rfl
  have htarget : target =
      Finset.Ioc 0 R ×ˢ (Finset.Ioc 0 R).filter Squarefree := rfl
  have himageSubset :
      source.image main4WilsonSquareDecomposition ⊆ target := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    rw [hsource] at hn
    rw [htarget]
    exact main4WilsonSquareDecomposition_mem_product hn
  have himageSum :
      (∑ x ∈ source.image main4WilsonSquareDecomposition,
          main4WilsonSquareDecompositionWeight x) =
        ∑ n ∈ source, 1 / (n : ℝ) := by
    rw [Finset.sum_image (main4WilsonSquareDecomposition_injective_on R)]
    apply Finset.sum_congr rfl
    intro n hn
    apply main4WilsonSquareDecompositionWeight_apply
    have hn' : n ∈ Finset.Ioc 0 R := by simpa only [source] using hn
    exact (Finset.mem_Ioc.mp hn').1
  have himageLe :
      (∑ x ∈ source.image main4WilsonSquareDecomposition,
          main4WilsonSquareDecompositionWeight x) ≤
        ∑ x ∈ target, main4WilsonSquareDecompositionWeight x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg himageSubset
    intro x _hx _hnot
    unfold main4WilsonSquareDecompositionWeight
    positivity
  have htargetSum :
      (∑ x ∈ target, main4WilsonSquareDecompositionWeight x) =
        (∑ s ∈ Finset.Ioc 0 R, 1 / (s : ℝ) ^ 2) *
          main4WilsonSquarefreeHarmonicMass R := by
    rw [htarget, Finset.sum_product]
    unfold main4WilsonSquarefreeHarmonicMass
    simp only [main4WilsonSquareDecompositionWeight]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [Finset.mul_sum]
  have hsquares :
      (∑ s ∈ Finset.Ioc 0 R, 1 / (s : ℝ) ^ 2) ≤ 2 := by
    rcases R with _ | R
    · simp
    · have hset : Finset.Ioc 0 (R + 1) =
          insert 1 (Finset.Icc 2 (R + 1)) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_insert,
          Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      have htail := sum_reciprocal_square_le
        (S := 2) (N := R + 1) (by norm_num)
      norm_num at htail ⊢
      linarith
  have hmassNonneg : 0 ≤ main4WilsonSquarefreeHarmonicMass R := by
    unfold main4WilsonSquarefreeHarmonicMass
    positivity
  have hharmonic :
      (harmonic R : ℝ) = ∑ n ∈ source, 1 / (n : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
    apply Finset.sum_congr
    · ext n
      simp only [source, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    · intro n _hn
      rfl
  calc
    (harmonic R : ℝ) =
        ∑ n ∈ source, 1 / (n : ℝ) := hharmonic
    _ = ∑ x ∈ source.image main4WilsonSquareDecomposition,
          main4WilsonSquareDecompositionWeight x := himageSum.symm
    _ ≤ ∑ x ∈ target,
          main4WilsonSquareDecompositionWeight x := himageLe
    _ = (∑ s ∈ Finset.Ioc 0 R, 1 / (s : ℝ) ^ 2) *
          main4WilsonSquarefreeHarmonicMass R := htargetSum
    _ ≤ 2 * main4WilsonSquarefreeHarmonicMass R :=
      mul_le_mul_of_nonneg_right hsquares hmassNonneg

/-- Explicit logarithmic lower bound for the squarefree harmonic mass. -/
theorem half_log_add_one_le_main4WilsonSquarefreeHarmonicMass (R : ℕ) :
    (1 / 2 : ℝ) * Real.log (R + 1) ≤
      main4WilsonSquarefreeHarmonicMass R := by
  have hlog : Real.log (R + 1) ≤ (harmonic R : ℝ) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      log_add_one_le_harmonic R
  have hsqfree :=
    harmonic_le_two_mul_main4WilsonSquarefreeHarmonicMass R
  linarith

/-- A dummy bounding-sieve object carrying precisely the prime product and
local density needed to construct Wilson's neutralizer.  Its support and
weights play no role in the construction of the Selberg coefficients. -/
def main4WilsonHalfBoundingSieve (z : ℕ) : BoundingSieve where
  support := ∅
  prodPrimes := primorial z
  prodPrimes_squarefree := squarefree_primorial z
  weights := 0
  weights_nonneg := by simp
  totalMass := 0
  nu := main4WilsonHalfDensity
  nu_mult := main4WilsonHalfDensity_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpP
    rw [main4WilsonHalfDensity_apply_prime hp]
    exact inv_pos.mpr (mul_pos (by norm_num) (by exact_mod_cast hp.pos))
  nu_lt_one_of_prime := by
    intro p hp _hpP
    rw [main4WilsonHalfDensity_apply_prime hp]
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [inv_lt_one₀]
    · nlinarith
    · positivity

namespace BoundingSieve

@[simp]
theorem main4WilsonHalfBoundingSieve_prodPrimes (z : ℕ) :
    (main4WilsonHalfBoundingSieve z).prodPrimes = primorial z := rfl

@[simp]
theorem main4WilsonHalfBoundingSieve_nu (z n : ℕ) :
    (main4WilsonHalfBoundingSieve z).nu n = main4WilsonHalfDensity n := rfl

/-- The Selberg local factor for the half-dimensional density. -/
theorem main4WilsonHalf_selbergTerms_apply_prime {z p : ℕ}
    (hp : p.Prime) :
    (main4WilsonHalfBoundingSieve z).selbergTerms p =
      1 / (2 * (p : ℝ) - 1) := by
  rw [_root_.BoundingSieve.selbergTerms_apply,
    main4WilsonHalfBoundingSieve_nu,
    main4WilsonHalfDensity_apply_prime hp]
  simp only [hp.primeFactors, prod_singleton,
    main4WilsonHalfBoundingSieve_nu,
    main4WilsonHalfDensity_apply_prime hp]
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  field_simp

end BoundingSieve

/-- The Selberg terms restricted to the divisor lattice of the primorial. -/
def main4WilsonRestrictedHalfSelbergTerms (z : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n ∣ primorial z then
    (main4WilsonHalfBoundingSieve z).selbergTerms n else 0
  map_zero' := by simp [primorial_ne_zero]

theorem main4WilsonRestrictedHalfSelbergTerms_nonneg (z n : ℕ) :
    0 ≤ main4WilsonRestrictedHalfSelbergTerms z n := by
  change 0 ≤ if n ∣ primorial z then
    (main4WilsonHalfBoundingSieve z).selbergTerms n else 0
  split_ifs with hn
  · exact (main4WilsonHalfBoundingSieve z).selbergTerms_pos hn |>.le
  · rfl

/-- A squarefree integer below `z` divides the full primorial at `z`. -/
theorem dvd_primorial_of_squarefree_of_le {n z : ℕ}
    (hn : Squarefree n) (hnz : n ≤ z) :
    n ∣ primorial z := by
  calc
    n = ∏ p ∈ n.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hn).symm
    _ ∣ ∏ p ∈ Nat.primesLE z, p := by
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpDvd := Nat.dvd_of_mem_primeFactors hp
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpDvd).trans hnz,
          hpPrime⟩
    _ = primorial z := (primorial_eq_prod_primesLE z).symm

/-- On squarefree divisors, Wilson's complementary density divided by the
modulus is exactly the multiplicative density used by the Selberg sieve. -/
theorem main4WilsonComplementWeight_div_eq_halfDensity
    {d : ℕ} (hd : Squarefree d) :
    main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ) =
      main4WilsonHalfDensity d := by
  have hdCast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  unfold main4WilsonReciprocalDivisorComplementWeight main4WilsonHalfDensity
  rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero, hdCast,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  rw [main4WilsonReciprocalDivisorWeight_prime hpPrime]
  field_simp
  norm_num

/-- The local convolution factor dominates the reciprocal prime factor. -/
private theorem one_div_prime_le_two_mul_halfSelbergTerm
    {z p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) ≤
      2 * (main4WilsonHalfBoundingSieve z).selbergTerms p := by
  rw [BoundingSieve.main4WilsonHalf_selbergTerms_apply_prime hp]
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdenPos : (0 : ℝ) < 2 * p - 1 := by
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  rw [show 2 * (1 / (2 * (p : ℝ) - 1)) =
      2 / (2 * (p : ℝ) - 1) by ring]
  exact (div_le_div_iff₀ hpPos hdenPos).2 (by nlinarith)

private theorem one_div_eq_prod_primeFactors_one_div
    {n : ℕ} (hn : Squarefree n) :
    1 / (n : ℝ) = ∏ p ∈ n.primeFactors, 1 / (p : ℝ) := by
  simp only [one_div]
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hn]

/-- On a squarefree integer, the self-convolution of the half-dimensional
Selberg term dominates `1/n`. -/
private theorem one_div_le_halfSelbergTerms_convolution
    {z n : ℕ} (hn : Squarefree n) :
    1 / (n : ℝ) ≤
      ((main4WilsonHalfBoundingSieve z).selbergTerms *
        (main4WilsonHalfBoundingSieve z).selbergTerms) n := by
  let g := (main4WilsonHalfBoundingSieve z).selbergTerms
  have hg : g.IsMultiplicative :=
    (main4WilsonHalfBoundingSieve z).selbergTerms_isMultiplicative
  have hEuler := hg.prodPrimeFactors_add_of_squarefree hg hn
  calc
    1 / (n : ℝ) = ∏ p ∈ n.primeFactors, 1 / (p : ℝ) :=
      one_div_eq_prod_primeFactors_one_div hn
    _ ≤ ∏ p ∈ n.primeFactors, 2 * g p := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p hp
        exact one_div_prime_le_two_mul_halfSelbergTerm
          (z := z) (Nat.prime_of_mem_primeFactors hp)
    _ = (g * g) n := by
      rw [← hEuler]
      rw [ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero]
      apply Finset.prod_congr rfl
      intro p _hp
      simp only [ArithmeticFunction.add_apply]
      ring
    _ = ((main4WilsonHalfBoundingSieve z).selbergTerms *
        (main4WilsonHalfBoundingSieve z).selbergTerms) n := rfl

private theorem restrictedHalfSelbergTerms_convolution_apply
    {z n : ℕ} (hn : Squarefree n) (hnz : n ≤ z) :
    (main4WilsonRestrictedHalfSelbergTerms z *
        main4WilsonRestrictedHalfSelbergTerms z) n =
      ((main4WilsonHalfBoundingSieve z).selbergTerms *
        (main4WilsonHalfBoundingSieve z).selbergTerms) n := by
  have hnP : n ∣ primorial z := dvd_primorial_of_squarefree_of_le hn hnz
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hprod, _hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hxOne : x.1 ∣ n := ⟨x.2, hprod.symm⟩
  have hxTwo : x.2 ∣ n := ⟨x.1, by rw [mul_comm]; exact hprod.symm⟩
  change
    (if x.1 ∣ primorial z then
        (main4WilsonHalfBoundingSieve z).selbergTerms x.1 else 0) *
      (if x.2 ∣ primorial z then
        (main4WilsonHalfBoundingSieve z).selbergTerms x.2 else 0) = _
  rw [if_pos (hxOne.trans hnP), if_pos (hxTwo.trans hnP)]

/-- The restricted convolution retains the same squarefree lower bound. -/
private theorem one_div_le_restrictedHalfSelbergTerms_convolution
    {z n : ℕ} (hn : Squarefree n) (hnz : n ≤ z) :
    1 / (n : ℝ) ≤
      (main4WilsonRestrictedHalfSelbergTerms z *
        main4WilsonRestrictedHalfSelbergTerms z) n := by
  rw [restrictedHalfSelbergTerms_convolution_apply hn hnz]
  exact one_div_le_halfSelbergTerms_convolution hn

/-- Natural-cutoff version of the half-dimensional Selberg mass. -/
def main4WilsonHalfSelbergCutoffMass (z R : ℕ) : ℝ :=
  ∑ d ∈ (primorial z).divisors,
    if d ≤ R then (main4WilsonHalfBoundingSieve z).selbergTerms d else 0

private theorem sum_Ioc_restrictedHalfSelbergTerms_eq_cutoffMass
    (z R : ℕ) :
    (∑ d ∈ Finset.Ioc 0 R,
        main4WilsonRestrictedHalfSelbergTerms z d) =
      main4WilsonHalfSelbergCutoffMass z R := by
  unfold main4WilsonHalfSelbergCutoffMass
  change (∑ d ∈ Finset.Ioc 0 R,
      if d ∣ primorial z then
        (main4WilsonHalfBoundingSieve z).selbergTerms d else 0) = _
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdPos, hdR⟩, hdP⟩
      exact ⟨⟨hdP, primorial_ne_zero z⟩, hdR⟩
    · rintro ⟨⟨hdP, _hPne⟩, hdR⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdP (primorial_pos z), hdR⟩, hdP⟩
  · intro d _hd
    rfl

/-- Squaring the cutoff mass captures every squarefree reciprocal term below
the cutoff. -/
theorem main4WilsonSquarefreeHarmonicMass_le_halfSelbergCutoffMass_sq
    {z R : ℕ} (hRz : R ≤ z) :
    main4WilsonSquarefreeHarmonicMass R ≤
      main4WilsonHalfSelbergCutoffMass z R ^ 2 := by
  let r := main4WilsonRestrictedHalfSelbergTerms z
  have hrNonneg : ∀ n : ℕ, 0 ≤ r n :=
    main4WilsonRestrictedHalfSelbergTerms_nonneg z
  have hconvNonneg : ∀ n : ℕ, 0 ≤ (r * r) n := by
    intro n
    simp only [ArithmeticFunction.mul_apply]
    exact Finset.sum_nonneg fun x _hx ↦
      mul_nonneg (hrNonneg x.1) (hrNonneg x.2)
  calc
    main4WilsonSquarefreeHarmonicMass R =
        ∑ n ∈ (Finset.Ioc 0 R).filter Squarefree,
          1 / (n : ℝ) := rfl
    _ ≤ ∑ n ∈ (Finset.Ioc 0 R).filter Squarefree,
          (r * r) n := by
      apply Finset.sum_le_sum
      intro n hn
      exact one_div_le_restrictedHalfSelbergTerms_convolution
        (Finset.mem_filter.mp hn).2
        ((Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2.trans hRz)
    _ ≤ ∑ n ∈ Finset.Ioc 0 R, (r * r) n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset Squarefree (Finset.Ioc 0 R))
      intro n _hn _hnot
      exact hconvNonneg n
    _ = ∑ x ∈ (Finset.Ioc 0 R ×ˢ Finset.Ioc 0 R).filter
          (fun x ↦ x.1 * x.2 ≤ R), r x.1 * r x.2 :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter r r R
    _ ≤ ∑ x ∈ Finset.Ioc 0 R ×ˢ Finset.Ioc 0 R,
          r x.1 * r x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun x : ℕ × ℕ ↦ x.1 * x.2 ≤ R)
          (Finset.Ioc 0 R ×ˢ Finset.Ioc 0 R))
      intro x _hx _hnot
      exact mul_nonneg (hrNonneg x.1) (hrNonneg x.2)
    _ = (∑ d ∈ Finset.Ioc 0 R, r d) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [sq]
    _ = main4WilsonHalfSelbergCutoffMass z R ^ 2 := by
      rw [sum_Ioc_restrictedHalfSelbergTerms_eq_cutoffMass]

/-- The concrete Selberg sieve used for a natural cutoff root `R+1`.
Its coefficient level is the square `(R+1)^2`, while its prime product
contains every prime up to `R+1`. -/
def main4WilsonHalfSelbergSieve (R : ℕ) : SelbergSieve where
  toBoundingSieve := main4WilsonHalfBoundingSieve (R + 1)
  level := ((R + 1 : ℕ) : ℝ) ^ 2
  one_le_level := by
    have h : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
    nlinarith [sq_nonneg (((R + 1 : ℕ) : ℝ) - 1)]

@[simp]
theorem main4WilsonHalfSelbergSieve_level (R : ℕ) :
    (main4WilsonHalfSelbergSieve R).level =
      (((R + 1) ^ 2 : ℕ) : ℝ) := by
  simp [main4WilsonHalfSelbergSieve]

@[simp]
theorem main4WilsonHalfSelbergSieve_prodPrimes (R : ℕ) :
    (main4WilsonHalfSelbergSieve R).toBoundingSieve.prodPrimes =
      primorial (R + 1) := rfl

/-- The optimizer's real-square cutoff is exactly the natural cutoff `R+1`
for the concrete half-dimensional sieve. -/
theorem main4SelbergBoundingSum_half_eq_cutoffMass (R : ℕ) :
    main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R) =
      main4WilsonHalfSelbergCutoffMass (R + 1) (R + 1) := by
  unfold main4SelbergBoundingSum main4WilsonHalfSelbergCutoffMass
  dsimp only [main4WilsonHalfSelbergSieve, main4WilsonHalfBoundingSieve]
  apply Finset.sum_congr rfl
  intro d _hd
  have hiff :
      (d : ℝ) ^ 2 ≤ ((R + 1 : ℕ) : ℝ) ^ 2 ↔ d ≤ R + 1 := by
    rw [sq_le_sq₀ (Nat.cast_nonneg d) (Nat.cast_nonneg (R + 1))]
    exact_mod_cast Iff.rfl
  simp only [hiff]

/-- Explicit half-dimensional lower bound for the exact Selberg optimizer
denominator.  No Wirsing or Selberg--Delange theorem is needed. -/
theorem sqrt_half_log_add_two_le_main4SelbergBoundingSum_half (R : ℕ) :
    Real.sqrt ((1 / 2 : ℝ) * Real.log (R + 2)) ≤
      main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R) := by
  have hlog :=
    half_log_add_one_le_main4WilsonSquarefreeHarmonicMass (R + 1)
  have hconv :=
    main4WilsonSquarefreeHarmonicMass_le_halfSelbergCutoffMass_sq
      (z := R + 1) (R := R + 1) le_rfl
  have hsq :
      (1 / 2 : ℝ) * Real.log (R + 2) ≤
        main4WilsonHalfSelbergCutoffMass (R + 1) (R + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hlog.trans hconv
  rw [main4SelbergBoundingSum_half_eq_cutoffMass]
  rw [Real.sqrt_le_iff]
  have hmassPos :
      0 < main4WilsonHalfSelbergCutoffMass (R + 1) (R + 1) := by
    rw [← main4SelbergBoundingSum_half_eq_cutoffMass]
    exact main4SelbergBoundingSum_pos (main4WilsonHalfSelbergSieve R)
  exact ⟨hmassPos.le, hsq⟩

/-- For the concrete sieve, the divisor main sum in the neutralizer floor
expansion is the optimizer's exact reciprocal bounding sum. -/
theorem main4WilsonNeutralizerDivisorMainSum_halfSelberg_eq_inv (R : ℕ) :
    main4WilsonNeutralizerDivisorMainSum
        (primorial (R + 1))
        (main4SelbergMuPlus (main4WilsonHalfSelbergSieve R)) =
      (main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R))⁻¹ := by
  let s := main4WilsonHalfSelbergSieve R
  calc
    main4WilsonNeutralizerDivisorMainSum
        (primorial (R + 1)) (main4SelbergMuPlus s) =
        s.toBoundingSieve.mainSum (main4SelbergMuPlus s) := by
      unfold main4WilsonNeutralizerDivisorMainSum
        BoundingSieve.mainSum
      rw [show s.toBoundingSieve.prodPrimes = primorial (R + 1) by rfl]
      apply Finset.sum_congr rfl
      intro d hdP
      have hdSquarefree : Squarefree d :=
        (squarefree_primorial (R + 1)).squarefree_of_dvd
          (Nat.dvd_of_mem_divisors hdP)
      have hdensity :=
        main4WilsonComplementWeight_div_eq_halfDensity hdSquarefree
      change
        main4SelbergMuPlus s d *
              main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ) =
          main4SelbergMuPlus s d * main4WilsonHalfDensity d
      rw [show main4SelbergMuPlus s d *
          main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ) =
          main4SelbergMuPlus s d *
            (main4WilsonReciprocalDivisorComplementWeight d / (d : ℝ)) by
        ring, hdensity]
    _ = (main4SelbergBoundingSum s)⁻¹ :=
      main4Selberg_mainSum_eq_inv s
    _ = (main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R))⁻¹ := rfl

/-- Exact total-mass handoff: the optimized main term plus the coarse cubic
coefficient error at the natural level `(R+1)^2`. -/
theorem main4WilsonNeutralizerTotalMass_halfSelberg_le_inv_add_cube
    (R M : ℕ) :
    main4WilsonNeutralizerTotalMass
        (primorial (R + 1)) M
        (main4SelbergMuPlus (main4WilsonHalfSelbergSieve R)) ≤
      (M : ℝ) *
          (main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R))⁻¹ +
        ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := by
  let s := main4WilsonHalfSelbergSieve R
  calc
    main4WilsonNeutralizerTotalMass
        (primorial (R + 1)) M (main4SelbergMuPlus s) ≤
        (M : ℝ) * main4WilsonNeutralizerDivisorMainSum
            (primorial (R + 1)) (main4SelbergMuPlus s) +
          main4WilsonNeutralizerCoefficientMass
            (primorial (R + 1)) (main4SelbergMuPlus s) :=
      main4WilsonNeutralizerTotalMass_le_main_add_coefficientMass
        (primorial (R + 1)) M (primorial_ne_zero (R + 1))
          (main4SelbergMuPlus s)
    _ ≤ (M : ℝ) * (main4SelbergBoundingSum s)⁻¹ +
          ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := by
      rw [main4WilsonNeutralizerDivisorMainSum_halfSelberg_eq_inv R]
      gcongr
      apply main4WilsonNeutralizerCoefficientMass_selberg_le_cube
        s ((R + 1) ^ 2)
      exact main4WilsonHalfSelbergSieve_level R
    _ = (M : ℝ) *
          (main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R))⁻¹ +
        ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := rfl

/-- Fully explicit half-dimensional neutralizer mass bound. -/
theorem main4WilsonNeutralizerTotalMass_halfSelberg_le_div_sqrt_add_cube
    (R M : ℕ) :
    main4WilsonNeutralizerTotalMass
        (primorial (R + 1)) M
        (main4SelbergMuPlus (main4WilsonHalfSelbergSieve R)) ≤
      (M : ℝ) /
          Real.sqrt ((1 / 2 : ℝ) * Real.log (R + 2)) +
        ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := by
  let root : ℝ := Real.sqrt ((1 / 2 : ℝ) * Real.log (R + 2))
  have hlogPos : 0 < Real.log ((R : ℝ) + 2) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R + 2 by omega)
  have hrootPos : 0 < root := by
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) hlogPos)
  have hbounding :=
    sqrt_half_log_add_two_le_main4SelbergBoundingSum_half R
  have hinv :
      (main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R))⁻¹ ≤
        root⁻¹ :=
    inv_anti₀ hrootPos hbounding
  calc
    main4WilsonNeutralizerTotalMass
        (primorial (R + 1)) M
        (main4SelbergMuPlus (main4WilsonHalfSelbergSieve R)) ≤
        (M : ℝ) *
            (main4SelbergBoundingSum (main4WilsonHalfSelbergSieve R))⁻¹ +
          ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) :=
      main4WilsonNeutralizerTotalMass_halfSelberg_le_inv_add_cube R M
    _ ≤ (M : ℝ) * root⁻¹ +
          ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := by
      gcongr
    _ = (M : ℝ) /
          Real.sqrt ((1 / 2 : ℝ) * Real.log (R + 2)) +
        ((((R + 1) ^ 2 : ℕ) : ℝ) ^ 3) := by
      rw [div_eq_mul_inv]

end

end PellPaper
