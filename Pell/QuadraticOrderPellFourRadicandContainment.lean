import Pell.QuadraticOrderPellTraceNorm

/-!
# The `D = 4d` containment for the Pell order

This module treats the second branch of a positive fundamental discriminant:
`D = 4d`, where `d` is squarefree and congruent to `2` or `3` modulo `4`.
For the rational quadratic algebra with radicand `4d`, it proves the concrete
elementwise containment

`2 * 𝓞_K ⊆ ℤ[√(4d)]`.

The proof does not identify the integral closure.  Trace and norm first show
that the imaginary coordinate has denominator at most four.  The norm identity
modulo four forces the resulting numerator to be even, improving this to the
required half-integrality.  This is a containment statement only; it does not
make a claim about quotient units or their exponent.
-/

namespace PellPaper

private theorem square_mod_four_of_even {z : ℤ} (hz : Even z) :
    z ^ 2 ≡ 0 [ZMOD 4] := by
  obtain ⟨k, hk⟩ := hz
  rw [Int.modEq_iff_dvd]
  refine ⟨-(k ^ 2), ?_⟩
  rw [hk]
  ring

private theorem square_mod_four_of_odd {z : ℤ} (hz : Odd z) :
    z ^ 2 ≡ 1 [ZMOD 4] := by
  obtain ⟨k, hk⟩ := hz
  rw [Int.modEq_iff_dvd]
  refine ⟨-(k ^ 2 + k), ?_⟩
  rw [hk]
  ring

/-- In the `d ≡ 2, 3 (mod 4)` branch, the norm identity forces the
imaginary-coordinate numerator to be even. -/
private theorem even_of_norm_parity
    (d t n b : ℤ) (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h : t ^ 2 - 4 * n = d * b ^ 2) : Even b := by
  by_contra hbeven
  have hodd : Odd b := Int.not_even_iff_odd.mp hbeven
  have hmain : t ^ 2 ≡ d * b ^ 2 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    linarith [h]
  have hb : b ^ 2 ≡ 1 [ZMOD 4] := square_mod_four_of_odd hodd
  have hdmod : d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4] := by
    rcases hd with hd | hd
    · left
      change d % 4 = 2 % 4
      norm_num [hd]
    · right
      change d % 4 = 3 % 4
      norm_num [hd]
  have hright : d * b ^ 2 ≡ 2 [ZMOD 4] ∨ d * b ^ 2 ≡ 3 [ZMOD 4] := by
    rcases hdmod with hdmod | hdmod
    · left
      exact hdmod.mul hb
    · right
      exact hdmod.mul hb
  have hleft : t ^ 2 ≡ 0 [ZMOD 4] ∨ t ^ 2 ≡ 1 [ZMOD 4] := by
    rcases Int.even_or_odd t with ht | ht
    · exact Or.inl (square_mod_four_of_even ht)
    · exact Or.inr (square_mod_four_of_odd ht)
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · exact (by norm_num [Int.ModEq] : ¬ ((0 : ℤ) ≡ 2 [ZMOD 4]))
      (hleft.symm.trans (hmain.trans hright))
  · exact (by norm_num [Int.ModEq] : ¬ ((0 : ℤ) ≡ 3 [ZMOD 4]))
      (hleft.symm.trans (hmain.trans hright))
  · exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 2 [ZMOD 4]))
      (hleft.symm.trans (hmain.trans hright))
  · exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 3 [ZMOD 4]))
      (hleft.symm.trans (hmain.trans hright))

/-- For `D = 4d`, with `d` squarefree and `d ≡ 2, 3 (mod 4)`, every
algebraic integer has half-integral coordinates in the basis `1, √D`. -/
theorem quadraticOrderPellHalfIntegralCoordinates_of_four_mul_squarefree_mod_four
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (4 * (d : ℤ)))]
    (x : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (4 * (d : ℤ)))) :
    quadraticOrderPellHalfIntegralCoordinates (4 * (d : ℤ))
      (x : rationalQuadraticAlgebra (4 * (d : ℤ))) := by
  obtain ⟨t, ht⟩ := rationalQuadraticAlgebra_exists_int_two_mul_re (4 * (d : ℤ)) x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm (4 * (d : ℤ)) x
  have hq : (d : ℚ) *
      (4 * (x : rationalQuadraticAlgebra (4 * (d : ℤ))).im) ^ 2 =
        (t ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [ht, hn]
    norm_num
    ring
  obtain ⟨b, hb⟩ := rat_eq_int_of_squarefree_mul_sq_eq_int hdsq
    (4 * (x : rationalQuadraticAlgebra (4 * (d : ℤ))).im)
    ⟨t ^ 2 - 4 * n, hq⟩
  have hEqQ : (d : ℚ) * (b : ℚ) ^ 2 = (t ^ 2 - 4 * n : ℤ) := by
    rw [hb]
    exact hq
  have hEqZ : t ^ 2 - 4 * n = (d : ℤ) * b ^ 2 := by
    exact_mod_cast hEqQ.symm
  have hdmodZ : (d : ℤ) % 4 = 2 ∨ (d : ℤ) % 4 = 3 := by
    exact_mod_cast hdmod
  obtain ⟨c, hc⟩ := even_of_norm_parity (d : ℤ) t n b hdmodZ hEqZ
  have hcQ : (c : ℚ) = 2 *
      (x : rationalQuadraticAlgebra (4 * (d : ℤ))).im := by
    have hcQ0 : (b : ℚ) = (c : ℚ) + c := by
      exact_mod_cast hc
    linarith
  exact ⟨t, c, ht, hcQ⟩

/-- The elementwise form of `2 * 𝓞_K ⊆ ℤ[√(4d)]` in the
`d ≡ 2, 3 (mod 4)` squarefree branch. -/
theorem quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_four_mul_squarefree_mod_four
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (4 * (d : ℤ)))]
    (x : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (4 * (d : ℤ)))) :
    ∃ z : ℤ√(4 * (d : ℤ)),
      quadraticOrderPellEmbeddingToRingOfIntegers (4 * (d : ℤ)) z = (2 : ℤ) • x :=
  (quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_iff
    (4 * (d : ℤ)) x).mpr
    (quadraticOrderPellHalfIntegralCoordinates_of_four_mul_squarefree_mod_four
      d hdsq hdmod x)

/-- The preceding coordinate result in the natural-number radicand form
`((4 * d : ℕ) : ℤ)`, which is the form occurring in the definition of a
positive fundamental discriminant. -/
theorem quadraticOrderPellHalfIntegralCoordinates_of_nat_four_mul_squarefree_mod_four
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))]
    (x : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :
    quadraticOrderPellHalfIntegralCoordinates ((4 * d : ℕ) : ℤ)
      (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) := by
  have hfact : Fact (rationalQuadraticAlgebraNoRationalRoot (4 * (d : ℤ))) :=
    ⟨by simpa [Nat.cast_mul] using
      (Fact.out : rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))⟩
  simpa [Nat.cast_mul] using
    (@quadraticOrderPellHalfIntegralCoordinates_of_four_mul_squarefree_mod_four
      d hdsq hdmod hfact x)

/-- The natural-number-radicand form of
`2 * 𝓞_K ⊆ ℤ[√(4d)]`, ready to use after rewriting a positive fundamental
discriminant as `4 * d`. -/
theorem quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_nat_four_mul_squarefree_mod_four
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))]
    (x : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :
    ∃ z : ℤ√((4 * d : ℕ) : ℤ),
      quadraticOrderPellEmbeddingToRingOfIntegers ((4 * d : ℕ) : ℤ) z = (2 : ℤ) • x := by
  have hfact : Fact (rationalQuadraticAlgebraNoRationalRoot (4 * (d : ℤ))) :=
    ⟨by simpa [Nat.cast_mul] using
      (Fact.out : rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))⟩
  simpa [Nat.cast_mul] using
    (@quadraticOrderPellEmbeddingToRingOfIntegers_two_zsmul_mem_range_of_four_mul_squarefree_mod_four
      d hdsq hdmod hfact x)

end PellPaper
