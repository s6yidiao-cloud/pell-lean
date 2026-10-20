import Pell.QuadraticIdealNormEulerConcrete

/-!
# A divisor bound for ideal-norm fibres in real quadratic fields

At a positive fundamental discriminant, the project already identifies the
number of maximal-order ideals of norm `n` with the `n`th coefficient of
`zeta * L(chi_D)`.  Expanding that convolution and using `‖chi_D(d)‖ <= 1`
gives the elementary bound by the number of positive divisors of `n`.

This is the ideal-counting input used at the manuscript.  It contains
no asymptotic estimate and no Weil-bound input.
-/

namespace PellPaper

open NumberField

noncomputable section

local instance rationalQuadraticAlgebra_idealNormDivisorBound_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The number of integral ideals of positive norm `n` in the real quadratic
maximal order of fundamental discriminant `D` is at most `tau(n)`. -/
theorem rationalQuadraticAlgebra_card_idealNormFibre_le_card_divisors
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (n : ℕ) (hn : n ≠ 0) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    Nat.card {I : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = n} ≤
        n.divisors.card := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  let chi := kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD
  have hcoeff := rationalQuadraticAlgebra_raw_idealNormCoefficient_eq_zetaMul
    D hD hn
  have hbound :
      (Nat.card {I : Ideal (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = n} : ℝ) ≤
          n.divisors.card := by
    calc
      (Nat.card {I : Ideal (NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = n} : ℝ) =
          ‖(Nat.card {I : Ideal (NumberField.RingOfIntegers
            (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = n} : ℂ)‖ := by
            simp
      _ = ‖chi.zetaMul n‖ := by rw [hcoeff]
      _ = ‖∑ d ∈ n.divisors, toArithmeticFunction (chi ·) d‖ := by
        rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
      _ ≤ ∑ d ∈ n.divisors, ‖toArithmeticFunction (chi ·) d‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
        simpa [toArithmeticFunction, hd0] using DirichletCharacter.norm_le_one chi d
      _ = n.divisors.card := by simp
  exact_mod_cast hbound

end
end PellPaper
