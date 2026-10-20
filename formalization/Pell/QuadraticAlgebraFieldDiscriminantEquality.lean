import Pell.QuadraticAlgebraFieldDiscriminant
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# The field discriminant of the concrete quadratic algebra

For each positive fundamental discriminant `D`, this module proves that the
Mathlib field discriminant of `ℚ(√D)` is exactly `D`.  The two branches of the
fundamental-discriminant predicate use explicit rational bases:

* for squarefree `D ≡ 1 [MOD 4]`, the basis `1, (1 + √D) / 2`;
* for `D = 4d`, with `d` squarefree and `d ≡ 2, 3 [MOD 4]`, the basis
  `1, √D / 2`.

The proof is not a conditional wrapper: it computes each rational-basis
discriminant and compares it to Mathlib's integral basis through integral
change-of-basis coefficients.  The key coordinate argument refines the
existing half-integrality containment to show that every algebraic integer
has integral coordinates in the appropriate displayed basis.
-/

namespace PellPaper

noncomputable section

open Module

local instance rationalQuadraticAlgebra_discriminantEquality_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

private noncomputable def oddCoordinateEquiv (D : ℕ) :
    rationalQuadraticAlgebra (D : ℤ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun z := ![z.re - z.im, 2 * z.im]
  invFun f := ⟨f 0 + f 1 / 2, f 1 / 2⟩
  left_inv z := by
    ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_add' x y := by
    funext i
    fin_cases i
    · change (x + y).re - (x + y).im =
        (x.re - x.im) + (y.re - y.im)
      simp
      ring
    · change 2 * (x + y).im = 2 * x.im + 2 * y.im
      simp
      ring
  map_smul' c x := by
    funext i
    fin_cases i
    · change (c • x).re - (c • x).im = c • (x.re - x.im)
      simp
      ring
    · change 2 * (c • x).im = c • (2 * x.im)
      simp
      ring

private noncomputable def oddBasis (D : ℕ) :
    Basis (Fin 2) ℚ (rationalQuadraticAlgebra (D : ℤ)) :=
  Basis.ofEquivFun (oddCoordinateEquiv D)

private def oddGenerator (D : ℕ) : rationalQuadraticAlgebra (D : ℤ) :=
  ⟨1 / 2, 1 / 2⟩

private theorem rationalQuadraticAlgebra_one_re (D : ℕ) :
    (1 : rationalQuadraticAlgebra (D : ℤ)).re = 1 := rfl

private theorem rationalQuadraticAlgebra_one_im (D : ℕ) :
    (1 : rationalQuadraticAlgebra (D : ℤ)).im = 0 := rfl

private theorem oddBasis_zero (D : ℕ) : oddBasis D 0 = 1 := by
  unfold oddBasis
  rw [Basis.coe_ofEquivFun]
  change (⟨(Pi.single 0 1 : Fin 2 → ℚ) 0 +
      (Pi.single 0 1 : Fin 2 → ℚ) 1 / 2,
      (Pi.single 0 1 : Fin 2 → ℚ) 1 / 2⟩ : rationalQuadraticAlgebra (D : ℤ)) =
    ⟨1, 0⟩
  norm_num [Pi.single_apply]

private theorem oddBasis_one (D : ℕ) :
    oddBasis D 1 = oddGenerator D := by
  unfold oddBasis
  rw [Basis.coe_ofEquivFun]
  change (⟨(Pi.single 1 1 : Fin 2 → ℚ) 0 +
      (Pi.single 1 1 : Fin 2 → ℚ) 1 / 2,
      (Pi.single 1 1 : Fin 2 → ℚ) 1 / 2⟩ : rationalQuadraticAlgebra (D : ℤ)) =
    oddGenerator D
  simp [oddGenerator]

private theorem discr_oddBasis (D : ℕ) :
    Algebra.discr ℚ (oddBasis D) = (D : ℚ) := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [oddBasis_zero, oddBasis_one]
  repeat' rw [rationalQuadraticAlgebra_trace_apply]
  simp [oddGenerator, rationalQuadraticAlgebra_one_re]
  ring

private theorem exists_int_one_sub_div_four (D : ℕ) (hDmod : D % 4 = 1) :
    ∃ c : ℤ, (c : ℚ) = (1 - (D : ℤ)) / 4 := by
  have hsplit := Nat.mod_add_div D 4
  have hD : D = 4 * (D / 4) + 1 := by
    omega
  have hDq : (D : ℚ) = 4 * ((D / 4 : ℕ) : ℚ) + 1 := by
    exact_mod_cast hD
  refine ⟨-(D / 4 : ℤ), ?_⟩
  change -((D / 4 : ℕ) : ℚ) = (1 - (D : ℚ)) / 4
  rw [hDq]
  ring

private theorem oddGenerator_isIntegral (D : ℕ) (hDmod : D % 4 = 1) :
    IsIntegral ℤ (oddGenerator D) := by
  obtain ⟨c, hc⟩ := exists_int_one_sub_div_four D hDmod
  refine ⟨Polynomial.X ^ 2 - (Polynomial.X - Polynomial.C c), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_sub_C (by simp)]
    norm_num
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change oddGenerator D ^ 2 - (oddGenerator D - (c : ℚ)) = 0
    ext <;> simp [oddGenerator, hc, pow_two] <;> ring

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

private theorem even_sub_of_square_norm_eq_of_mod_four_one
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
    have htSq : t ^ 2 ≡ 0 [ZMOD 4] := square_mod_four_of_even ht
    have hbSq : b ^ 2 ≡ 1 [ZMOD 4] := square_mod_four_of_odd hb
    have hright : D * b ^ 2 ≡ 1 [ZMOD 4] := by
      simpa using hD.mul hbSq
    exact (by norm_num [Int.ModEq] : ¬ ((0 : ℤ) ≡ 1 [ZMOD 4]))
      (htSq.symm.trans (hmain.trans hright))
  · intro hb
    by_contra hte
    have ht : Odd t := Int.not_even_iff_odd.mp hte
    have htSq : t ^ 2 ≡ 1 [ZMOD 4] := square_mod_four_of_odd ht
    have hbSq : b ^ 2 ≡ 0 [ZMOD 4] := square_mod_four_of_even hb
    have hright : D * b ^ 2 ≡ 0 [ZMOD 4] := by
      simpa using hD.mul hbSq
    exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 0 [ZMOD 4]))
      (htSq.symm.trans (hmain.trans hright))

private theorem oddCoordinateEquiv_coordinates_are_integral
    (D : ℕ) (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
    (i : Fin 2) :
    IsIntegral ℤ ((oddCoordinateEquiv D) (x : rationalQuadraticAlgebra (D : ℤ)) i) := by
  obtain ⟨t, b, ht, hb⟩ :=
    quadraticOrderPellHalfIntegralCoordinates_of_squarefree D hDsq x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm (D : ℤ) x
  have hq : (D : ℚ) * (2 * (x : rationalQuadraticAlgebra (D : ℤ)).im) ^ 2 =
      (t ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [ht, hn]
    norm_num
    ring
  have hEqZ : t ^ 2 - 4 * n = (D : ℤ) * b ^ 2 := by
    have hq' : (t ^ 2 - 4 * n : ℤ) = (D : ℚ) * (b : ℚ) ^ 2 := by
      rw [hb]
      exact hq.symm
    exact_mod_cast hq'
  obtain ⟨a, ha⟩ := even_sub_of_square_norm_eq_of_mod_four_one
    (D : ℤ) t n b (by exact_mod_cast hDmod) hEqZ
  have haZ : t - b = 2 * a := by
    simpa [two_mul] using ha
  have haQ : (t : ℚ) - (b : ℚ) = 2 * (a : ℚ) := by
    exact_mod_cast haZ
  have hcoord0 : (a : ℚ) =
      (x : rationalQuadraticAlgebra (D : ℤ)).re -
        (x : rationalQuadraticAlgebra (D : ℤ)).im := by
    rw [ht, hb] at haQ
    linarith
  fin_cases i
  · change IsIntegral ℤ ((x : rationalQuadraticAlgebra (D : ℤ)).re -
      (x : rationalQuadraticAlgebra (D : ℤ)).im)
    rw [← hcoord0]
    exact isIntegral_intCast a
  · change IsIntegral ℤ (2 * (x : rationalQuadraticAlgebra (D : ℤ)).im)
    rw [← hb]
    exact isIntegral_intCast b

private def oddGeneratorRingOfIntegers (D : ℕ) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)) :=
  ⟨oddGenerator D, oddGenerator_isIntegral D hDmod⟩

@[simp]
private theorem coe_oddGeneratorRingOfIntegers (D : ℕ) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    ((oddGeneratorRingOfIntegers D hDmod :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
        rationalQuadraticAlgebra (D : ℤ)) = oddGenerator D := rfl

private theorem integralBasis_repr_isIntegral
    (D : ℕ) [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
    (i : Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))) :
    IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra (D : ℤ))).repr
        (x : rationalQuadraticAlgebra (D : ℤ)) i) := by
  rw [NumberField.integralBasis_repr_apply]
  exact isIntegral_intCast ((NumberField.RingOfIntegers.basis
    (rationalQuadraticAlgebra (D : ℤ))).repr x i)

private theorem oddBasis_toMatrix_integralBasis_integral
    (D : ℕ) (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (i : Fin 2) (j : Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))) :
    IsIntegral ℤ ((oddBasis D).toMatrix
      (NumberField.integralBasis (rationalQuadraticAlgebra (D : ℤ))) i j) := by
  rw [Basis.toMatrix_apply]
  change IsIntegral ℤ ((oddCoordinateEquiv D)
    (NumberField.integralBasis (rationalQuadraticAlgebra (D : ℤ)) j) i)
  rw [NumberField.integralBasis_apply]
  exact oddCoordinateEquiv_coordinates_are_integral D hDsq hDmod
    (NumberField.RingOfIntegers.basis (rationalQuadraticAlgebra (D : ℤ)) j) i

private theorem integralBasis_toMatrix_oddBasis_integral
    (D : ℕ) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (i : Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
    (j : Fin 2) :
    IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra (D : ℤ))).toMatrix (oddBasis D) i j) := by
  rw [Basis.toMatrix_apply]
  fin_cases j
  · change IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra (D : ℤ))).repr (oddBasis D 0) i)
    rw [oddBasis_zero]
    change IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra (D : ℤ))).repr
        ((1 : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (D : ℤ))) : rationalQuadraticAlgebra (D : ℤ)) i)
    exact integralBasis_repr_isIntegral D 1 i
  · change IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra (D : ℤ))).repr (oddBasis D 1) i)
    rw [oddBasis_one]
    rw [← coe_oddGeneratorRingOfIntegers D hDmod]
    exact integralBasis_repr_isIntegral D (oddGeneratorRingOfIntegers D hDmod) i

private theorem rationalQuadraticAlgebra_fieldDiscriminant_eq_of_squarefree_mod_four_one
    (D : ℕ) (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) = (D : ℤ) := by
  have hcomparison : Algebra.discr ℚ (oddBasis D) =
      Algebra.discr ℚ (NumberField.integralBasis
        (rationalQuadraticAlgebra (D : ℤ))) :=
    Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
      (rationalQuadraticAlgebra (D : ℤ))
      (fun i j ↦ oddBasis_toMatrix_integralBasis_integral D hDsq hDmod i j)
      (fun i j ↦ integralBasis_toMatrix_oddBasis_integral D hDmod i j)
  have hq : (NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) : ℚ) = (D : ℚ) := by
    calc
      (NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) : ℚ) =
          Algebra.discr ℚ (NumberField.integralBasis
            (rationalQuadraticAlgebra (D : ℤ))) :=
        NumberField.coe_discr (rationalQuadraticAlgebra (D : ℤ))
      _ = Algebra.discr ℚ (oddBasis D) := hcomparison.symm
      _ = (D : ℚ) := discr_oddBasis D
  exact_mod_cast hq

private noncomputable def evenCoordinateEquiv (d : ℕ) :
    rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun z := ![z.re, 2 * z.im]
  invFun f := ⟨f 0, f 1 / 2⟩
  left_inv z := by
    ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_add' x y := by
    funext i
    fin_cases i
    · change (x + y).re = x.re + y.re
      simp
    · change 2 * (x + y).im = 2 * x.im + 2 * y.im
      simp
      ring
  map_smul' c x := by
    funext i
    fin_cases i
    · change (c • x).re = c • x.re
      simp
    · change 2 * (c • x).im = c • (2 * x.im)
      simp
      ring

private noncomputable def evenBasis (d : ℕ) :
    Basis (Fin 2) ℚ (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) :=
  Basis.ofEquivFun (evenCoordinateEquiv d)

private def evenGenerator (d : ℕ) :
    rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ) :=
  ⟨0, 1 / 2⟩

private theorem evenBasis_zero (d : ℕ) : evenBasis d 0 = 1 := by
  unfold evenBasis
  rw [Basis.coe_ofEquivFun]
  change (⟨(Pi.single 0 1 : Fin 2 → ℚ) 0,
      (Pi.single 0 1 : Fin 2 → ℚ) 1 / 2⟩ :
      rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) = ⟨1, 0⟩
  norm_num [Pi.single_apply]

private theorem evenBasis_one (d : ℕ) : evenBasis d 1 = evenGenerator d := by
  unfold evenBasis
  rw [Basis.coe_ofEquivFun]
  change (⟨(Pi.single 1 1 : Fin 2 → ℚ) 0,
      (Pi.single 1 1 : Fin 2 → ℚ) 1 / 2⟩ :
      rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) = evenGenerator d
  simp [evenGenerator]

private theorem discr_evenBasis (d : ℕ) :
    Algebra.discr ℚ (evenBasis d) = ((4 * d : ℕ) : ℚ) := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [evenBasis_zero, evenBasis_one]
  repeat' rw [rationalQuadraticAlgebra_trace_apply]
  simp [evenGenerator, rationalQuadraticAlgebra_one_re]
  ring

private theorem evenGenerator_isIntegral (d : ℕ) :
    IsIntegral ℤ (evenGenerator d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (d : ℤ),
    Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  change evenGenerator d ^ 2 - (d : ℚ) = 0
  ext <;> simp [evenGenerator, pow_two]
  field_simp
  norm_num

private theorem even_of_square_norm_eq_of_four_dvd
    (D t n b : ℤ) (hD : (4 : ℤ) ∣ D)
    (h : t ^ 2 - 4 * n = D * b ^ 2) : Even t := by
  by_contra hte
  have ht : Odd t := Int.not_even_iff_odd.mp hte
  have hmain : t ^ 2 ≡ D * b ^ 2 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    linarith [h]
  obtain ⟨q, hq⟩ := hD
  have hright : D * b ^ 2 ≡ 0 [ZMOD 4] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(q * b ^ 2), ?_⟩
    rw [hq]
    ring
  have htSq : t ^ 2 ≡ 1 [ZMOD 4] := square_mod_four_of_odd ht
  exact (by norm_num [Int.ModEq] : ¬ ((1 : ℤ) ≡ 0 [ZMOD 4]))
    (htSq.symm.trans (hmain.trans hright))

private theorem evenCoordinateEquiv_coordinates_are_integral
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))]
    (x : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)))
    (i : Fin 2) :
    IsIntegral ℤ ((evenCoordinateEquiv d)
      (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) i) := by
  obtain ⟨t, b, ht, hb⟩ :=
    quadraticOrderPellHalfIntegralCoordinates_of_nat_four_mul_squarefree_mod_four
      d hdsq hdmod x
  obtain ⟨n, hn⟩ := rationalQuadraticAlgebra_exists_int_norm
    ((4 * d : ℕ) : ℤ) x
  have hq : ((4 * d : ℕ) : ℚ) *
      (2 * (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)).im) ^ 2 =
      (t ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [ht, hn]
    norm_num
    ring_nf
    rfl
  have hEqZ : t ^ 2 - 4 * n = ((4 * d : ℕ) : ℤ) * b ^ 2 := by
    have hq' : (t ^ 2 - 4 * n : ℤ) =
        ((4 * d : ℕ) : ℚ) * (b : ℚ) ^ 2 := by
      rw [hb]
      exact hq.symm
    exact_mod_cast hq'
  have hfour : (4 : ℤ) ∣ ((4 * d : ℕ) : ℤ) := by
    refine ⟨(d : ℤ), ?_⟩
    norm_num [Nat.cast_mul]
  obtain ⟨a, ha⟩ := even_of_square_norm_eq_of_four_dvd
    ((4 * d : ℕ) : ℤ) t n b hfour hEqZ
  have haZ : t = 2 * a := by
    simpa [two_mul] using ha
  have haQ : (t : ℚ) = 2 * (a : ℚ) := by
    exact_mod_cast haZ
  have hcoord0 : (a : ℚ) =
      (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)).re := by
    rw [ht] at haQ
    linarith
  fin_cases i
  · change IsIntegral ℤ
      ((x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)).re)
    rw [← hcoord0]
    exact isIntegral_intCast a
  · change IsIntegral ℤ
      (2 * (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)).im)
    rw [← hb]
    exact isIntegral_intCast b

private def evenGeneratorRingOfIntegers (d : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))] :
    NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) :=
  ⟨evenGenerator d, evenGenerator_isIntegral d⟩

@[simp]
private theorem coe_evenGeneratorRingOfIntegers (d : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))] :
    ((evenGeneratorRingOfIntegers d : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :
        rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) = evenGenerator d := rfl

private theorem evenBasis_toMatrix_integralBasis_integral
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))]
    (i : Fin 2) (j : Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)))) :
    IsIntegral ℤ ((evenBasis d).toMatrix
      (NumberField.integralBasis
        (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) i j) := by
  rw [Basis.toMatrix_apply]
  change IsIntegral ℤ ((evenCoordinateEquiv d)
    (NumberField.integralBasis
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) j) i)
  rw [NumberField.integralBasis_apply]
  exact evenCoordinateEquiv_coordinates_are_integral d hdsq hdmod
    (NumberField.RingOfIntegers.basis
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) j) i

private theorem integralBasis_toMatrix_evenBasis_integral
    (d : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))]
    (i : Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))))
    (j : Fin 2) :
    IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))).toMatrix (evenBasis d) i j) := by
  rw [Basis.toMatrix_apply]
  fin_cases j
  · change IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))).repr (evenBasis d 0) i)
    rw [evenBasis_zero]
    change IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))).repr
        ((1 : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :
            rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) i)
    exact integralBasis_repr_isIntegral ((4 * d : ℕ)) 1 i
  · change IsIntegral ℤ ((NumberField.integralBasis
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))).repr (evenBasis d 1) i)
    rw [evenBasis_one]
    rw [← coe_evenGeneratorRingOfIntegers d]
    exact integralBasis_repr_isIntegral ((4 * d : ℕ))
      (evenGeneratorRingOfIntegers d) i

private theorem rationalQuadraticAlgebra_fieldDiscriminant_eq_of_four_mul_squarefree_mod_four
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))] :
    NumberField.discr (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) =
      ((4 * d : ℕ) : ℤ) := by
  have hcomparison : Algebra.discr ℚ (evenBasis d) =
      Algebra.discr ℚ (NumberField.integralBasis
        (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :=
    Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))
      (fun i j ↦ evenBasis_toMatrix_integralBasis_integral d hdsq hdmod i j)
      (fun i j ↦ integralBasis_toMatrix_evenBasis_integral d i j)
  have hq : (NumberField.discr
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) : ℚ) = ((4 * d : ℕ) : ℚ) := by
    calc
      (NumberField.discr
          (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)) : ℚ) =
          Algebra.discr ℚ (NumberField.integralBasis
            (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :=
        NumberField.coe_discr (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))
      _ = Algebra.discr ℚ (evenBasis d) := hcomparison.symm
      _ = ((4 * d : ℕ) : ℚ) := discr_evenBasis d
  exact_mod_cast hq

theorem rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant D hD =
      (D : ℤ) := by
  unfold rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  rcases hD.2 with hodd | hfour
  · exact rationalQuadraticAlgebra_fieldDiscriminant_eq_of_squarefree_mod_four_one
      D hodd.1 hodd.2
  · obtain ⟨d, hD, hdsq, hdmod⟩ := hfour
    subst D
    exact rationalQuadraticAlgebra_fieldDiscriminant_eq_of_four_mul_squarefree_mod_four
      d hdsq hdmod

/-- At an odd positive fundamental discriminant, every algebraic integer has
integer coordinates in the basis `1, (1 + √D) / 2`. -/
theorem rationalQuadraticAlgebra_integerCoordinates_of_squarefree_mod_four_one
    (D : ℕ) (hDsq : Squarefree D) (hDmod : D % 4 = 1)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (x : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
    ∃ u v : ℤ,
      (u : ℚ) = (x : rationalQuadraticAlgebra (D : ℤ)).re -
        (x : rationalQuadraticAlgebra (D : ℤ)).im ∧
      (v : ℚ) = 2 * (x : rationalQuadraticAlgebra (D : ℤ)).im := by
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (oddCoordinateEquiv_coordinates_are_integral D hDsq hDmod x 0)
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (oddCoordinateEquiv_coordinates_are_integral D hDsq hDmod x 1)
  exact ⟨u, v, hu, hv⟩

/-- At a fundamental discriminant `4d`, every algebraic integer has integer
coordinates in the basis `1, √(4d) / 2`. -/
theorem rationalQuadraticAlgebra_integerCoordinates_of_four_mul_squarefree_mod_four
    (d : ℕ) (hdsq : Squarefree d) (hdmod : d % 4 = 2 ∨ d % 4 = 3)
    [Fact (rationalQuadraticAlgebraNoRationalRoot ((4 * d : ℕ) : ℤ))]
    (x : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ))) :
    ∃ u v : ℤ,
      (u : ℚ) = (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)).re ∧
      (v : ℚ) = 2 * (x : rationalQuadraticAlgebra ((4 * d : ℕ) : ℤ)).im := by
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (evenCoordinateEquiv_coordinates_are_integral d hdsq hdmod x 0)
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (evenCoordinateEquiv_coordinates_are_integral d hdsq hdmod x 1)
  exact ⟨u, v, hu, hv⟩

end

end PellPaper
