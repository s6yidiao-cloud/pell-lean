import Pell.ShiftedSquareNormalizedExplicitCoordinates
import Mathlib.Tactic

/-!
# Bounded fibres of the shifted-square coordinate encoding

For fixed integral basis, primitive coordinate pairs, contents, and `C₀`,
the exact factorization and norm equations determine the original triple
`(d,w,n)` uniquely.  This is the algebraic bounded-fibre step in the
uniformity lemma; finite chart/sign/conjugation choices can be counted outside
this exact fibre.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareCoordinateFiber_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- A shifted-square solution represented with fixed coordinate data. -/
structure ShiftedSquareFixedCoordinateSolution
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (t c : ℤ) (C₀ r ell : ℕ) (x y : Fin 2 → ℤ) where
  d : ℕ
  w : ℕ
  n : ℕ
  equation : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a
  factorization :
    ((r : ℤ) • shiftedSquareIntegralBasisElement basis x) ^ 2 *
        ((ell : ℤ) • shiftedSquareIntegralBasisElement basis y) =
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ^ 2 *
        shiftedSquareZetaInteger equation
  source_norm :
    (r : ℤ) ^ 2 * |shiftedSquareExplicitNormFormEval t c x| =
      ((shiftedSquareD₀ d * C₀ : ℕ) : ℤ)
  target_norm :
    (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
      ((w * C₀ ^ 2 : ℕ) : ℤ)

/-- Equality of the normalized quadratic elements recovers first `q₂` and
then `n`. -/
theorem shiftedSquare_q₂_eq_and_n_eq_of_zetaInteger_eq
    {a : ℤ} {d₁ w₁ n₁ d₂ w₂ n₂ : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq₁ : (d₁ : ℤ) ^ 2 * (w₁ : ℤ) = (n₁ : ℤ) ^ 2 + a}
    {heq₂ : (d₂ : ℤ) ^ 2 * (w₂ : ℤ) = (n₂ : ℤ) ^ 2 + a}
    (hζ : shiftedSquareZetaInteger heq₁ = shiftedSquareZetaInteger heq₂) :
    shiftedSquareQ₂ d₁ = shiftedSquareQ₂ d₂ ∧ n₁ = n₂ := by
  have hζfield := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)) =>
      (z : rationalQuadraticAlgebra (-a))) hζ
  simp only [coe_shiftedSquareZetaInteger] at hζfield
  have him := congrArg QuadraticAlgebra.im hζfield
  simp only [shiftedSquareZeta_im] at him
  have hqQ : (shiftedSquareQ₂ d₁ : ℚ) = (shiftedSquareQ₂ d₂ : ℚ) := by
    apply inv_injective
    simpa only [one_div] using him
  have hq : shiftedSquareQ₂ d₁ = shiftedSquareQ₂ d₂ := by
    exact_mod_cast hqQ
  have hre := congrArg QuadraticAlgebra.re hζfield
  simp only [shiftedSquareZeta_re] at hre
  rw [hq] at hre
  have hq0 : (shiftedSquareQ₂ d₂ : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (shiftedSquareQ₂_pos d₂))
  have hnQ : (n₁ : ℚ) = (n₂ : ℚ) := (div_left_inj' hq0).mp hre
  exact ⟨hq, by exact_mod_cast hnQ⟩

/-- For positive `C₀`, two solutions with identical fixed coordinate data
have identical original triples. -/
theorem shiftedSquareFixedCoordinateSolution_ext
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ} {C₀ r ell : ℕ} {x y : Fin 2 → ℤ}
    (hC₀ : 0 < C₀)
    (P₁ P₂ : ShiftedSquareFixedCoordinateSolution
      a basis t c C₀ r ell x y) : P₁ = P₂ := by
  have hscaled :
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ^ 2 *
          shiftedSquareZetaInteger P₁.equation =
        (C₀ : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) ^ 2 *
          shiftedSquareZetaInteger P₂.equation :=
    P₁.factorization.symm.trans P₂.factorization
  have hC₀ne :
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hC₀)
  have hζ : shiftedSquareZetaInteger P₁.equation =
      shiftedSquareZetaInteger P₂.equation :=
    mul_left_cancel₀ (pow_ne_zero 2 hC₀ne) hscaled
  obtain ⟨hq, hn⟩ :=
    shiftedSquare_q₂_eq_and_n_eq_of_zetaInteger_eq hζ
  have hd₀MulZ :
      ((shiftedSquareD₀ P₁.d * C₀ : ℕ) : ℤ) =
        ((shiftedSquareD₀ P₂.d * C₀ : ℕ) : ℤ) :=
    P₁.source_norm.symm.trans P₂.source_norm
  have hd₀Mul : shiftedSquareD₀ P₁.d * C₀ =
      shiftedSquareD₀ P₂.d * C₀ := by
    exact_mod_cast hd₀MulZ
  have hd₀ : shiftedSquareD₀ P₁.d = shiftedSquareD₀ P₂.d :=
    Nat.mul_right_cancel hC₀ hd₀Mul
  have hd : P₁.d = P₂.d := by
    calc
      P₁.d = shiftedSquareQ₂ P₁.d * shiftedSquareD₀ P₁.d :=
        (shiftedSquareQ₂_mul_D₀ P₁.d).symm
      _ = shiftedSquareQ₂ P₂.d * shiftedSquareD₀ P₂.d := by rw [hq, hd₀]
      _ = P₂.d := shiftedSquareQ₂_mul_D₀ P₂.d
  have hwMulZ : ((P₁.w * C₀ ^ 2 : ℕ) : ℤ) =
      ((P₂.w * C₀ ^ 2 : ℕ) : ℤ) :=
    P₁.target_norm.symm.trans P₂.target_norm
  have hwMul : P₁.w * C₀ ^ 2 = P₂.w * C₀ ^ 2 := by
    exact_mod_cast hwMulZ
  have hC₀sq : 0 < C₀ ^ 2 := pow_pos hC₀ 2
  have hw : P₁.w = P₂.w := Nat.mul_right_cancel hC₀sq hwMul
  cases P₁
  cases P₂
  simp_all

/-- The exact fixed-coordinate fibre is a subsingleton. -/
theorem shiftedSquareFixedCoordinateSolution_subsingleton
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ} {C₀ r ell : ℕ} {x y : Fin 2 → ℤ}
    (hC₀ : 0 < C₀) :
    Subsingleton (ShiftedSquareFixedCoordinateSolution
      a basis t c C₀ r ell x y) :=
  ⟨shiftedSquareFixedCoordinateSolution_ext hC₀⟩

/-- Every finite exact fixed-coordinate fibre has cardinality at most one. -/
theorem card_shiftedSquareFixedCoordinateSolution_le_one
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ} {C₀ r ell : ℕ} {x y : Fin 2 → ℤ}
    (hC₀ : 0 < C₀)
    (S : Finset (ShiftedSquareFixedCoordinateSolution
      a basis t c C₀ r ell x y)) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro P₁ _ P₂ _
  exact shiftedSquareFixedCoordinateSolution_ext hC₀ P₁ P₂

end

end PellPaper
