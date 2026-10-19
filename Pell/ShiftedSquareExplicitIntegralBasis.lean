import Pell.ShiftedSquareMinkowskiC0Nu
import Pell.QuadraticAlgebraFieldDiscriminantEquality
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic

/-!
# An explicit integral basis for signed shifted-square quadratic fields

Let `D = -a` be the signed squarefree radicand in the shifted-square route.
This file constructs the full ring-of-integers basis

* `1, (1 + sqrt D) / 2` when `D = 1 (mod 4)`;
* `1, sqrt D` otherwise.

The coordinate argument is valid for either sign of `D`.  It extends the
existing positive-radicand denominator proof by passing through `Int.natAbs`,
then performs the required parity calculation modulo four.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareExplicitIntegralBasis_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Signed version of the squarefree rational-denominator lemma. -/
theorem rat_eq_int_of_int_squarefree_mul_sq_eq_int
    {D : ℤ} (hD : Squarefree D) (q : ℚ)
    (h : ∃ z : ℤ, (D : ℚ) * q ^ 2 = (z : ℚ)) :
    ∃ b : ℤ, (b : ℚ) = q := by
  have hDabs : Squarefree D.natAbs := Int.squarefree_natAbs.mpr hD
  obtain ⟨z, hz⟩ := h
  apply rat_eq_int_of_squarefree_mul_sq_eq_int hDabs q
  refine ⟨z.natAbs, ?_⟩
  calc
    (D.natAbs : ℚ) * q ^ 2 = |(D : ℚ)| * q ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    _ = |(D : ℚ) * q ^ 2| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg q)]
    _ = |(z : ℚ)| := congrArg abs hz
    _ = (z.natAbs : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]

/-- Every algebraic integer in a signed squarefree quadratic algebra has
half-integral coordinates in the displayed basis `1, sqrt D`. -/
theorem rationalQuadraticAlgebra_halfIntegralCoordinates_of_int_squarefree
    (D : ℤ) (hD : Squarefree D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ∃ t b : ℤ,
      (t : ℚ) = 2 * (x : rationalQuadraticAlgebra D).re ∧
      (b : ℚ) = 2 * (x : rationalQuadraticAlgebra D).im := by
  obtain ⟨t, ht⟩ := rationalQuadraticAlgebra_exists_int_two_mul_re D x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm D x
  have him : ∃ b : ℤ,
      (b : ℚ) = 2 * (x : rationalQuadraticAlgebra D).im := by
    apply rat_eq_int_of_int_squarefree_mul_sq_eq_int hD
    refine ⟨t ^ 2 - 4 * n, ?_⟩
    push_cast
    rw [ht, hn]
    ring
  obtain ⟨b, hb⟩ := him
  exact ⟨t, b, ht, hb⟩

private theorem shiftedSquare_square_mod_four_of_even {z : ℤ} (hz : Even z) :
    z ^ 2 ≡ 0 [ZMOD 4] := by
  obtain ⟨k, hk⟩ := hz
  rw [Int.modEq_iff_dvd]
  refine ⟨-(k ^ 2), ?_⟩
  rw [hk]
  ring

private theorem shiftedSquare_square_mod_four_of_odd {z : ℤ} (hz : Odd z) :
    z ^ 2 ≡ 1 [ZMOD 4] := by
  obtain ⟨k, hk⟩ := hz
  rw [Int.modEq_iff_dvd]
  refine ⟨-(k ^ 2 + k), ?_⟩
  rw [hk]
  ring

private theorem shiftedSquare_even_sub_of_square_norm_eq_of_mod_four_one
    (D t n b : ℤ) (hDmod : D % 4 = 1)
    (h : t ^ 2 - 4 * n = D * b ^ 2) : Even (t - b) := by
  rw [Int.even_sub]
  have hmain : t ^ 2 ≡ D * b ^ 2 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    linarith [h]
  have hD : D ≡ 1 [ZMOD 4] := by
    change D % 4 = 1 % 4
    norm_num [hDmod]
  constructor
  · intro ht
    by_contra hbe
    have hb : Odd b := Int.not_even_iff_odd.mp hbe
    have htSq := shiftedSquare_square_mod_four_of_even ht
    have hbSq := shiftedSquare_square_mod_four_of_odd hb
    have hright : D * b ^ 2 ≡ 1 [ZMOD 4] := by
      simpa using hD.mul hbSq
    exact (by norm_num [Int.ModEq] : ¬ ((0 : ℤ) ≡ 1 [ZMOD 4]))
      (htSq.symm.trans (hmain.trans hright))
  · intro hb
    by_contra hte
    have ht : Odd t := Int.not_even_iff_odd.mp hte
    have htSq := shiftedSquare_square_mod_four_of_odd ht
    have hbSq := shiftedSquare_square_mod_four_of_even hb
    have hright : D * b ^ 2 ≡ 0 [ZMOD 4] := by
      simpa using hD.mul hbSq
    exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 0 [ZMOD 4]))
      (htSq.symm.trans (hmain.trans hright))

/-- In the `D = 1 (mod 4)` branch, every algebraic integer has integer
coordinates in `1, (1 + sqrt D) / 2`. -/
theorem rationalQuadraticAlgebra_integerCoordinates_of_int_squarefree_mod_four_one
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ∃ u v : ℤ,
      (u : ℚ) = (x : rationalQuadraticAlgebra D).re -
        (x : rationalQuadraticAlgebra D).im ∧
      (v : ℚ) = 2 * (x : rationalQuadraticAlgebra D).im := by
  obtain ⟨t, b, ht, hb⟩ :=
    rationalQuadraticAlgebra_halfIntegralCoordinates_of_int_squarefree D hDsq x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm D x
  have hEq : t ^ 2 - 4 * n = D * b ^ 2 := by
    have hq : (t ^ 2 - 4 * n : ℤ) =
        (D : ℚ) * (b : ℚ) ^ 2 := by
      push_cast
      rw [ht, hb, hn]
      ring
    exact_mod_cast hq
  obtain ⟨u, hu⟩ :=
    shiftedSquare_even_sub_of_square_norm_eq_of_mod_four_one
      D t n b hDmod hEq
  have huZ : t - b = 2 * u := by simpa [two_mul] using hu
  have huQ : (t : ℚ) - (b : ℚ) = 2 * (u : ℚ) := by
    exact_mod_cast huZ
  refine ⟨u, b, ?_, hb⟩
  rw [ht, hb] at huQ
  linarith

private theorem shiftedSquare_not_four_dvd_of_squarefree
    {D : ℤ} (hD : Squarefree D) : ¬ (4 : ℤ) ∣ D := by
  intro hfour
  have hunit : IsUnit (2 : ℤ) := hD 2 (by simpa [pow_two] using hfour)
  rcases Int.isUnit_iff.mp hunit with hunit | hunit <;> omega

private theorem shiftedSquare_mod_four_eq_two_or_three
    (D : ℤ) (hD : Squarefree D) (hDmod : D % 4 ≠ 1) :
    D % 4 = 2 ∨ D % 4 = 3 := by
  have hmodNonneg : 0 ≤ D % 4 := Int.emod_nonneg D (by norm_num)
  have hmodLt : D % 4 < 4 := Int.emod_lt_of_pos D (by norm_num)
  have hmodZero : D % 4 ≠ 0 := by
    intro hzero
    apply shiftedSquare_not_four_dvd_of_squarefree hD
    exact Int.dvd_iff_emod_eq_zero.mpr hzero
  omega

private theorem shiftedSquare_even_b_of_square_norm_eq_of_nonodd_squarefree
    (D t n b : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    (h : t ^ 2 - 4 * n = D * b ^ 2) : Even b := by
  by_contra hbEven
  have hb : Odd b := Int.not_even_iff_odd.mp hbEven
  have hbSq := shiftedSquare_square_mod_four_of_odd hb
  have hmain : t ^ 2 ≡ D * b ^ 2 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    linarith [h]
  rcases shiftedSquare_mod_four_eq_two_or_three D hDsq hDmod with hDtwo | hDthree
  · have hD : D ≡ 2 [ZMOD 4] := by
      change D % 4 = 2 % 4
      norm_num [hDtwo]
    have hright : D * b ^ 2 ≡ 2 [ZMOD 4] := by
      simpa using hD.mul hbSq
    by_cases htEven : Even t
    · have htSq := shiftedSquare_square_mod_four_of_even htEven
      exact (by norm_num [Int.ModEq] : ¬ ((0 : ℤ) ≡ 2 [ZMOD 4]))
        (htSq.symm.trans (hmain.trans hright))
    · have htSq := shiftedSquare_square_mod_four_of_odd
        (Int.not_even_iff_odd.mp htEven)
      exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 2 [ZMOD 4]))
        (htSq.symm.trans (hmain.trans hright))
  · have hD : D ≡ 3 [ZMOD 4] := by
      change D % 4 = 3 % 4
      norm_num [hDthree]
    have hright : D * b ^ 2 ≡ 3 [ZMOD 4] := by
      simpa using hD.mul hbSq
    by_cases htEven : Even t
    · have htSq := shiftedSquare_square_mod_four_of_even htEven
      exact (by norm_num [Int.ModEq] : ¬ ((0 : ℤ) ≡ 3 [ZMOD 4]))
        (htSq.symm.trans (hmain.trans hright))
    · have htSq := shiftedSquare_square_mod_four_of_odd
        (Int.not_even_iff_odd.mp htEven)
      exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 3 [ZMOD 4]))
        (htSq.symm.trans (hmain.trans hright))

private theorem shiftedSquare_even_t_of_square_norm_eq_of_even_b
    (D t n b : ℤ) (hb : Even b)
    (h : t ^ 2 - 4 * n = D * b ^ 2) : Even t := by
  by_contra htEven
  have htSq := shiftedSquare_square_mod_four_of_odd
    (Int.not_even_iff_odd.mp htEven)
  have hmain : t ^ 2 ≡ D * b ^ 2 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    linarith [h]
  have hbSq := shiftedSquare_square_mod_four_of_even hb
  have hright : D * b ^ 2 ≡ 0 [ZMOD 4] := by
    simpa using (Int.ModEq.refl D).mul hbSq
  exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 0 [ZMOD 4]))
    (htSq.symm.trans (hmain.trans hright))

/-- Outside the `D = 1 (mod 4)` branch, every algebraic integer has integer
coordinates in `1, sqrt D`. -/
theorem rationalQuadraticAlgebra_integerCoordinates_of_int_squarefree_not_mod_four_one
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ∃ u v : ℤ,
      (u : ℚ) = (x : rationalQuadraticAlgebra D).re ∧
      (v : ℚ) = (x : rationalQuadraticAlgebra D).im := by
  obtain ⟨t, b, ht, hb⟩ :=
    rationalQuadraticAlgebra_halfIntegralCoordinates_of_int_squarefree D hDsq x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm D x
  have hEq : t ^ 2 - 4 * n = D * b ^ 2 := by
    have hq : (t ^ 2 - 4 * n : ℤ) =
        (D : ℚ) * (b : ℚ) ^ 2 := by
      push_cast
      rw [ht, hb, hn]
      ring
    exact_mod_cast hq
  have hbEven :=
    shiftedSquare_even_b_of_square_norm_eq_of_nonodd_squarefree
      D t n b hDsq hDmod hEq
  have htEven := shiftedSquare_even_t_of_square_norm_eq_of_even_b
    D t n b hbEven hEq
  obtain ⟨u, hu⟩ := htEven
  obtain ⟨v, hv⟩ := hbEven
  have huZ : t = 2 * u := by simpa [two_mul] using hu
  have hvZ : b = 2 * v := by simpa [two_mul] using hv
  have huQ : (t : ℚ) = 2 * (u : ℚ) := by exact_mod_cast huZ
  have hvQ : (b : ℚ) = 2 * (v : ℚ) := by exact_mod_cast hvZ
  refine ⟨u, v, ?_, ?_⟩
  · rw [ht] at huQ
    linarith
  · rw [hb] at hvQ
    linarith

/-! ## The odd integral basis -/

/-- The quadratic-algebra element `(1 + sqrt D) / 2`. -/
def shiftedSquareOddGenerator (D : ℤ) :
    rationalQuadraticAlgebra D :=
  ⟨1 / 2, 1 / 2⟩

private theorem exists_shiftedSquareOddConstant (D : ℤ)
    (hDmod : D % 4 = 1) :
    ∃ c : ℤ, D - 1 = 4 * c := by
  have hm : D ≡ 1 [ZMOD 4] := by
    change D % 4 = 1 % 4
    norm_num [hDmod]
  rw [Int.modEq_iff_dvd] at hm
  obtain ⟨k, hk⟩ := hm
  refine ⟨-k, ?_⟩
  linarith

theorem shiftedSquareOddGenerator_sq
    (D c : ℤ) (hc : D - 1 = 4 * c) :
    shiftedSquareOddGenerator D ^ 2 =
      shiftedSquareOddGenerator D +
        (c : rationalQuadraticAlgebra D) := by
  apply QuadraticAlgebra.ext
  · rw [pow_two]
    dsimp [shiftedSquareOddGenerator]
    change (1 / 2 : ℚ) * (1 / 2) + (D : ℚ) * (1 / 2) * (1 / 2) =
      1 / 2 + (c : ℚ)
    have hcQ : (D : ℚ) - 1 = 4 * (c : ℚ) := by exact_mod_cast hc
    linarith
  · norm_num [shiftedSquareOddGenerator, pow_two]

theorem shiftedSquareOddGenerator_isIntegral
    (D c : ℤ) (hc : D - 1 = 4 * c) :
    IsIntegral ℤ (shiftedSquareOddGenerator D) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C c, ?_, ?_⟩
  · monicity
    norm_num
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change shiftedSquareOddGenerator D ^ 2 -
      shiftedSquareOddGenerator D -
        (c : rationalQuadraticAlgebra D) = 0
    rw [shiftedSquareOddGenerator_sq D c hc]
    ring

/-- The integral element `(1 + sqrt D) / 2` when `D = 1 (mod 4)`. -/
def shiftedSquareOddGeneratorInteger
    (D c : ℤ) (hc : D - 1 = 4 * c)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  ⟨shiftedSquareOddGenerator D,
    shiftedSquareOddGenerator_isIntegral D c hc⟩

@[simp]
theorem coe_shiftedSquareOddGeneratorInteger
    (D c : ℤ) (hc : D - 1 = 4 * c)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((shiftedSquareOddGeneratorInteger D c hc :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) = shiftedSquareOddGenerator D := rfl

/-- The odd generator satisfies `omega^2 = omega + (D - 1) / 4` inside
the ring of integers. -/
theorem shiftedSquareOddGeneratorInteger_sq
    (D c : ℤ) (hc : D - 1 = 4 * c)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    shiftedSquareOddGeneratorInteger D c hc ^ 2 =
      shiftedSquareOddGeneratorInteger D c hc +
        (c : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) := by
  apply Subtype.ext
  change shiftedSquareOddGenerator D ^ 2 =
    shiftedSquareOddGenerator D + (c : rationalQuadraticAlgebra D)
  exact shiftedSquareOddGenerator_sq D c hc

private def shiftedSquareOddSpanLinearMap
    (D c : ℤ) (hc : D - 1 = 4 * c)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Fin 2 → ℤ) →ₗ[ℤ]
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D) where
  toFun f := f 0 • 1 + f 1 • shiftedSquareOddGeneratorInteger D c hc
  map_add' f g := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]
    simp

private theorem shiftedSquareOddSpanLinearMap_injective
    (D c : ℤ) (hc : D - 1 = 4 * c)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Function.Injective (shiftedSquareOddSpanLinearMap D c hc) := by
  intro f g hfg
  change f 0 • 1 + f 1 • shiftedSquareOddGeneratorInteger D c hc =
    g 0 • 1 + g 1 • shiftedSquareOddGeneratorInteger D c hc at hfg
  have hfield := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) =>
      (z : rationalQuadraticAlgebra D)) hfg
  simp only [map_add, map_zsmul, map_one,
    coe_shiftedSquareOddGeneratorInteger] at hfield
  have him := congrArg QuadraticAlgebra.im hfield
  have hre := congrArg QuadraticAlgebra.re hfield
  simp [shiftedSquareOddGenerator] at him hre
  have h1 : f 1 = g 1 := him
  have h0Q : (f 0 : ℚ) = (g 0 : ℚ) := by
    rw [h1] at hre
    linarith
  have h0 : f 0 = g 0 := by exact_mod_cast h0Q
  funext i
  fin_cases i
  · exact h0
  · exact h1

private theorem shiftedSquareOddSpanLinearMap_surjective
    (D c : ℤ) (hc : D - 1 = 4 * c)
    (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Function.Surjective (shiftedSquareOddSpanLinearMap D c hc) := by
  intro x
  obtain ⟨u, v, hu, hv⟩ :=
    rationalQuadraticAlgebra_integerCoordinates_of_int_squarefree_mod_four_one
      D hDsq hDmod x
  refine ⟨![u, v], ?_⟩
  change u • 1 + v • shiftedSquareOddGeneratorInteger D c hc = x
  apply Subtype.ext
  change (u : ℤ) • (1 : rationalQuadraticAlgebra D) +
    v • shiftedSquareOddGenerator D =
      (x : rationalQuadraticAlgebra D)
  apply QuadraticAlgebra.ext
  · simp [shiftedSquareOddGenerator]
    rw [hu, hv]
    ring
  · simp [shiftedSquareOddGenerator]
    rw [hv]
    ring

private noncomputable def shiftedSquareOddSpanLinearEquiv
    (D c : ℤ) (hc : D - 1 = 4 * c)
    (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Fin 2 → ℤ) ≃ₗ[ℤ]
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  LinearEquiv.ofBijective (shiftedSquareOddSpanLinearMap D c hc)
    ⟨shiftedSquareOddSpanLinearMap_injective D c hc,
      shiftedSquareOddSpanLinearMap_surjective D c hc hDsq hDmod⟩

/-- The actual ring-of-integers basis `1, (1 + sqrt D) / 2` in the signed
squarefree `D = 1 (mod 4)` branch. -/
noncomputable def shiftedSquareOddIntegralBasis
    (D c : ℤ) (hc : D - 1 = 4 * c)
    (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
  (Pi.basisFun ℤ (Fin 2)).map
    (shiftedSquareOddSpanLinearEquiv D c hc hDsq hDmod)

@[simp]
theorem shiftedSquareOddIntegralBasis_zero
    (D c : ℤ) (hc : D - 1 = 4 * c)
    (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    shiftedSquareOddIntegralBasis D c hc hDsq hDmod 0 = 1 := by
  simp [shiftedSquareOddIntegralBasis, shiftedSquareOddSpanLinearEquiv,
    shiftedSquareOddSpanLinearMap, Pi.basisFun_apply]

@[simp]
theorem shiftedSquareOddIntegralBasis_one
    (D c : ℤ) (hc : D - 1 = 4 * c)
    (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    shiftedSquareOddIntegralBasis D c hc hDsq hDmod 1 =
      shiftedSquareOddGeneratorInteger D c hc := by
  simp [shiftedSquareOddIntegralBasis, shiftedSquareOddSpanLinearEquiv,
    shiftedSquareOddSpanLinearMap, Pi.basisFun_apply]

/-! ## The non-odd integral basis -/

/-- The integral element `sqrt D`. -/
def shiftedSquareStandardGeneratorInteger
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  ⟨QuadraticAlgebra.omega, rationalQuadraticAlgebra_omega_isIntegral D⟩

@[simp]
theorem coe_shiftedSquareStandardGeneratorInteger
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((shiftedSquareStandardGeneratorInteger D :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) = QuadraticAlgebra.omega := rfl

/-- The standard generator satisfies `omega^2 = D` inside the ring of
integers. -/
theorem shiftedSquareStandardGeneratorInteger_sq
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    shiftedSquareStandardGeneratorInteger D ^ 2 =
      (D : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) := by
  apply Subtype.ext
  change (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 =
    (D : rationalQuadraticAlgebra D)
  simpa only [pow_two] using rationalQuadraticAlgebra_omega_sq D

private def shiftedSquareStandardSpanLinearMap
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Fin 2 → ℤ) →ₗ[ℤ]
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D) where
  toFun f := f 0 • 1 + f 1 • shiftedSquareStandardGeneratorInteger D
  map_add' f g := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]
    simp

private theorem shiftedSquareStandardSpanLinearMap_injective
    (D : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Function.Injective (shiftedSquareStandardSpanLinearMap D) := by
  intro f g hfg
  change f 0 • 1 + f 1 • shiftedSquareStandardGeneratorInteger D =
    g 0 • 1 + g 1 • shiftedSquareStandardGeneratorInteger D at hfg
  have hfield := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) =>
      (z : rationalQuadraticAlgebra D)) hfg
  simp only [map_add, map_zsmul, map_one,
    coe_shiftedSquareStandardGeneratorInteger] at hfield
  have him := congrArg QuadraticAlgebra.im hfield
  have hre := congrArg QuadraticAlgebra.re hfield
  simp at him hre
  have h1 : f 1 = g 1 := him
  have h0 : f 0 = g 0 := hre
  funext i
  fin_cases i
  · exact h0
  · exact h1

private theorem shiftedSquareStandardSpanLinearMap_surjective
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Function.Surjective (shiftedSquareStandardSpanLinearMap D) := by
  intro x
  obtain ⟨u, v, hu, hv⟩ :=
    rationalQuadraticAlgebra_integerCoordinates_of_int_squarefree_not_mod_four_one
      D hDsq hDmod x
  refine ⟨![u, v], ?_⟩
  change u • 1 + v • shiftedSquareStandardGeneratorInteger D = x
  apply Subtype.ext
  change (u : ℤ) • (1 : rationalQuadraticAlgebra D) +
    v • (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) =
      (x : rationalQuadraticAlgebra D)
  apply QuadraticAlgebra.ext
  · simp
    exact hu
  · simp
    exact hv

private noncomputable def shiftedSquareStandardSpanLinearEquiv
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Fin 2 → ℤ) ≃ₗ[ℤ]
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  LinearEquiv.ofBijective (shiftedSquareStandardSpanLinearMap D)
    ⟨shiftedSquareStandardSpanLinearMap_injective D,
      shiftedSquareStandardSpanLinearMap_surjective D hDsq hDmod⟩

/-- The actual ring-of-integers basis `1, sqrt D` in the signed squarefree
branch `D != 1 (mod 4)`. -/
noncomputable def shiftedSquareStandardIntegralBasis
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
  (Pi.basisFun ℤ (Fin 2)).map
    (shiftedSquareStandardSpanLinearEquiv D hDsq hDmod)

@[simp]
theorem shiftedSquareStandardIntegralBasis_zero
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    shiftedSquareStandardIntegralBasis D hDsq hDmod 0 = 1 := by
  simp [shiftedSquareStandardIntegralBasis,
    shiftedSquareStandardSpanLinearEquiv,
    shiftedSquareStandardSpanLinearMap, Pi.basisFun_apply]

@[simp]
theorem shiftedSquareStandardIntegralBasis_one
    (D : ℤ) (hDsq : Squarefree D) (hDmod : D % 4 ≠ 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    shiftedSquareStandardIntegralBasis D hDsq hDmod 1 =
      shiftedSquareStandardGeneratorInteger D := by
  simp [shiftedSquareStandardIntegralBasis,
    shiftedSquareStandardSpanLinearEquiv,
    shiftedSquareStandardSpanLinearMap, Pi.basisFun_apply]

/-! ## Exact shifted-square coordinates -/

/-- In the odd integral basis, the second coordinate of the normalized
shifted-square element is exactly `1` or `2`. -/
theorem shiftedSquareOddIntegralBasis_zeta_secondCoordinate
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (c : ℤ) (hc : -a - 1 = 4 * c) (hmod : (-a) % 4 = 1) :
    let b := shiftedSquareOddIntegralBasis (-a) c hc
      (shiftedSquare_radicand_squarefree ha) hmod
    b.repr (shiftedSquareZetaInteger heq) 1 = 1 ∨
      b.repr (shiftedSquareZetaInteger heq) 1 = 2 := by
  let b := shiftedSquareOddIntegralBasis (-a) c hc
    (shiftedSquare_radicand_squarefree ha) hmod
  change b.repr (shiftedSquareZetaInteger heq) 1 = 1 ∨
    b.repr (shiftedSquareZetaInteger heq) 1 = 2
  by_cases hdEven : Even d
  · left
    obtain ⟨k, hk⟩ :=
      (shiftedSquare_n_odd_of_even_d ha heq hdEven).exists_bit1
    have hzRing : shiftedSquareZetaInteger heq =
        (k : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) +
          shiftedSquareOddGeneratorInteger (-a) c hc := by
      apply Subtype.ext
      change shiftedSquareZeta a d n =
        ((k : ℚ) : rationalQuadraticAlgebra (-a)) +
          shiftedSquareOddGenerator (-a)
      apply QuadraticAlgebra.ext
      · change (n : ℚ) / (shiftedSquareQ₂ d : ℚ) =
          (k : ℚ) + 1 / 2
        rw [shiftedSquareQ₂_eq_two_of_even hdEven]
        have hkQ : (n : ℚ) = 2 * (k : ℚ) + 1 := by
          exact_mod_cast hk
        linarith
      · rw [QuadraticAlgebra.im_add]
        change 1 / (shiftedSquareQ₂ d : ℚ) = 0 + 1 / 2
        rw [shiftedSquareQ₂_eq_two_of_even hdEven]
        norm_num
    have hz : shiftedSquareZetaInteger heq =
        (k : ℤ) • b 0 + (1 : ℤ) • b 1 := by
      rw [show b 0 = 1 by
          exact shiftedSquareOddIntegralBasis_zero (-a) c hc
            (shiftedSquare_radicand_squarefree ha) hmod,
        show b 1 = shiftedSquareOddGeneratorInteger (-a) c hc by
          exact shiftedSquareOddIntegralBasis_one (-a) c hc
            (shiftedSquare_radicand_squarefree ha) hmod]
      simpa using hzRing
    have hcoord := congrArg (fun z => b.repr z 1) hz
    simp only [map_add, map_zsmul] at hcoord
    simpa using hcoord

  · right
    let m : ℤ := (n : ℤ) - 1
    have hzRing : shiftedSquareZetaInteger heq =
        (m : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) +
          shiftedSquareOddGeneratorInteger (-a) c hc +
          shiftedSquareOddGeneratorInteger (-a) c hc := by
      apply Subtype.ext
      change shiftedSquareZeta a d n =
        ((m : ℚ) : rationalQuadraticAlgebra (-a)) +
          shiftedSquareOddGenerator (-a) +
          shiftedSquareOddGenerator (-a)
      apply QuadraticAlgebra.ext
      · rw [QuadraticAlgebra.re_add, QuadraticAlgebra.re_add]
        change (n : ℚ) / (shiftedSquareQ₂ d : ℚ) =
          (m : ℚ) + 1 / 2 + 1 / 2
        rw [shiftedSquareQ₂_eq_one_of_not_even hdEven]
        dsimp [m]
        push_cast
        ring
      · rw [QuadraticAlgebra.im_add, QuadraticAlgebra.im_add]
        change 1 / (shiftedSquareQ₂ d : ℚ) = 0 + 1 / 2 + 1 / 2
        rw [shiftedSquareQ₂_eq_one_of_not_even hdEven]
        norm_num
    have hz : shiftedSquareZetaInteger heq =
        m • b 0 + (2 : ℤ) • b 1 := by
      rw [show b 0 = 1 by
          exact shiftedSquareOddIntegralBasis_zero (-a) c hc
            (shiftedSquare_radicand_squarefree ha) hmod,
        show b 1 = shiftedSquareOddGeneratorInteger (-a) c hc by
          exact shiftedSquareOddIntegralBasis_one (-a) c hc
            (shiftedSquare_radicand_squarefree ha) hmod]
      simpa [two_smul, add_assoc] using hzRing
    have hcoord := congrArg (fun z => b.repr z 1) hz
    simp only [map_add, map_zsmul] at hcoord
    simpa using hcoord

/-- In the standard integral basis, the shifted-square equation forces the
normalization denominator to be one, so the second coordinate is exactly
`1`. -/
theorem shiftedSquareStandardIntegralBasis_zeta_secondCoordinate
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (hmod : (-a) % 4 ≠ 1) :
    let b := shiftedSquareStandardIntegralBasis (-a)
      (shiftedSquare_radicand_squarefree ha) hmod
    b.repr (shiftedSquareZetaInteger heq) 1 = 1 := by
  let b := shiftedSquareStandardIntegralBasis (-a)
    (shiftedSquare_radicand_squarefree ha) hmod
  change b.repr (shiftedSquareZetaInteger heq) 1 = 1
  have hdNot : ¬ Even d := by
    intro hdEven
    apply hmod
    have hm := shiftedSquare_radicand_modEq_one_of_even_d ha heq hdEven
    change (-a) % 4 = 1 % 4 at hm
    norm_num at hm
    exact hm
  have hzRing : shiftedSquareZetaInteger heq =
      (n : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) +
        shiftedSquareStandardGeneratorInteger (-a) := by
    apply Subtype.ext
    change shiftedSquareZeta a d n =
      ((n : ℚ) : rationalQuadraticAlgebra (-a)) +
        (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a))
    apply QuadraticAlgebra.ext
    · change (n : ℚ) / (shiftedSquareQ₂ d : ℚ) = (n : ℚ) + 0
      rw [shiftedSquareQ₂_eq_one_of_not_even hdNot]
      simp
    · rw [QuadraticAlgebra.im_add]
      change 1 / (shiftedSquareQ₂ d : ℚ) = 0 + 1
      rw [shiftedSquareQ₂_eq_one_of_not_even hdNot]
      norm_num
  have hz : shiftedSquareZetaInteger heq =
      (n : ℤ) • b 0 + (1 : ℤ) • b 1 := by
    rw [show b 0 = 1 by
        exact shiftedSquareStandardIntegralBasis_zero (-a)
          (shiftedSquare_radicand_squarefree ha) hmod,
      show b 1 = shiftedSquareStandardGeneratorInteger (-a) by
        exact shiftedSquareStandardIntegralBasis_one (-a)
          (shiftedSquare_radicand_squarefree ha) hmod]
    simpa using hzRing
  have hcoord := congrArg (fun z => b.repr z 1) hz
  simp only [map_add, map_zsmul] at hcoord
  simpa using hcoord

/-- A single project-facing package for the signed squarefree radicand
`D = -a`.  It supplies an actual integral basis `1, omega`, a relation
`omega^2 = t * omega + c` with `t` equal to `0` or `1`, and proves that
the second coordinate of every normalized shifted-square element is exactly
`1` or `2` (hence nonzero and of absolute value at most `2`).

No sign condition on `a` is used, so the theorem covers both real and
imaginary quadratic fields. -/
theorem exists_shiftedSquareExplicitIntegralBasis_package
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) :
    ∃ (b : Module.Basis (Fin 2) ℤ
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
        (omega : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) (t c : ℤ),
      b 0 = 1 ∧
      b 1 = omega ∧
      (t = 0 ∨ t = 1) ∧
      omega ^ 2 =
        (t : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) * omega + c ∧
      ∀ {d w n : ℕ}
          (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a),
        let bζ : ℤ := b.repr (shiftedSquareZetaInteger heq) 1
        (bζ = 1 ∨ bζ = 2) ∧ bζ ≠ 0 ∧ |bζ| ≤ 2 := by
  by_cases hmod : (-a) % 4 = 1
  · obtain ⟨c, hc⟩ := exists_shiftedSquareOddConstant (-a) hmod
    let b := shiftedSquareOddIntegralBasis (-a) c hc
      (shiftedSquare_radicand_squarefree ha) hmod
    let omega := shiftedSquareOddGeneratorInteger (-a) c hc
    refine ⟨b, omega, 1, c, ?_, ?_, Or.inr rfl, ?_, ?_⟩
    · simpa only [b] using
        shiftedSquareOddIntegralBasis_zero (-a) c hc
          (shiftedSquare_radicand_squarefree ha) hmod
    · simpa only [b, omega] using
        shiftedSquareOddIntegralBasis_one (-a) c hc
          (shiftedSquare_radicand_squarefree ha) hmod
    · change shiftedSquareOddGeneratorInteger (-a) c hc ^ 2 =
        (1 : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) *
            shiftedSquareOddGeneratorInteger (-a) c hc + c
      rw [one_mul]
      exact shiftedSquareOddGeneratorInteger_sq (-a) c hc
    · intro d w n heq
      let bζ : ℤ := b.repr (shiftedSquareZetaInteger heq) 1
      have hcoord : bζ = 1 ∨ bζ = 2 := by
        dsimp only [bζ]
        simpa only [b] using
          shiftedSquareOddIntegralBasis_zeta_secondCoordinate
            ha heq c hc hmod
      refine ⟨hcoord, ?_, ?_⟩
      · change bζ ≠ 0
        rcases hcoord with hcoord | hcoord <;> omega
      · change |bζ| ≤ 2
        rcases hcoord with hcoord | hcoord <;> simp [hcoord]
  · let b := shiftedSquareStandardIntegralBasis (-a)
      (shiftedSquare_radicand_squarefree ha) hmod
    let omega := shiftedSquareStandardGeneratorInteger (-a)
    refine ⟨b, omega, 0, -a, ?_, ?_, Or.inl rfl, ?_, ?_⟩
    · simpa only [b] using
        shiftedSquareStandardIntegralBasis_zero (-a)
          (shiftedSquare_radicand_squarefree ha) hmod
    · simpa only [b, omega] using
        shiftedSquareStandardIntegralBasis_one (-a)
          (shiftedSquare_radicand_squarefree ha) hmod
    · change shiftedSquareStandardGeneratorInteger (-a) ^ 2 =
        (0 : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) *
            shiftedSquareStandardGeneratorInteger (-a) + (-a : ℤ)
      rw [zero_mul, zero_add]
      exact shiftedSquareStandardGeneratorInteger_sq (-a)
    · intro d w n heq
      let bζ : ℤ := b.repr (shiftedSquareZetaInteger heq) 1
      have hcoord : bζ = 1 := by
        dsimp only [bζ]
        simpa only [b] using
          shiftedSquareStandardIntegralBasis_zeta_secondCoordinate
            ha heq hmod
      refine ⟨Or.inl hcoord, ?_, ?_⟩
      · change bζ ≠ 0
        omega
      · change |bζ| ≤ 2
        simp [hcoord]

end

end PellPaper
