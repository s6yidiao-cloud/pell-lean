import Pell.ShiftedSquareCoordinateFiber

/-!
# An injective code for fixed-basis shifted-square solutions

Once the integral basis and its two structure constants are fixed, a
shifted-square solution is determined by `C₀`, the two contents, and the two
primitive coordinate pairs.  This module turns the existing subsingleton
fibre theorem into a literal injective finite-set encoding.  It is independent
of any analytic coordinate bounds.
-/

namespace PellPaper

noncomputable section

/-- The discrete data retained after fixing the integral basis and its
structure constants. -/
structure ShiftedSquareCoordinateCode where
  C₀ : ℕ
  r : ℕ
  ell : ℕ
  x : Fin 2 → ℤ
  y : Fin 2 → ℤ
deriving DecidableEq

/-- A shifted-square solution bundled with its fixed-coordinate code and the
positivity needed by the exact fibre theorem. -/
structure ShiftedSquareEncodedFixedBasisSolution
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (t c : ℤ) where
  C₀ : ℕ
  r : ℕ
  ell : ℕ
  x : Fin 2 → ℤ
  y : Fin 2 → ℤ
  C₀_pos : 0 < C₀
  solution : ShiftedSquareFixedCoordinateSolution
    a basis t c C₀ r ell x y

/-- Forget the uniquely determined original triple and retain its complete
fixed-basis coordinate code. -/
def ShiftedSquareEncodedFixedBasisSolution.code
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ}
    (P : ShiftedSquareEncodedFixedBasisSolution a basis t c) :
    ShiftedSquareCoordinateCode :=
  ⟨P.C₀, P.r, P.ell, P.x, P.y⟩

/-- The complete fixed-basis coordinate code is injective. -/
theorem ShiftedSquareEncodedFixedBasisSolution.code_injective
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ} :
    Function.Injective
      (@ShiftedSquareEncodedFixedBasisSolution.code a _ basis t c) := by
  intro P Q hcode
  rcases P with ⟨C₀, r, ell, x, y, hC₀, P⟩
  rcases Q with ⟨C₀', r', ell', x', y', hC₀', Q⟩
  simp only [ShiftedSquareEncodedFixedBasisSolution.code,
    ShiftedSquareCoordinateCode.mk.injEq] at hcode
  rcases hcode with ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hpoint : P = Q :=
    shiftedSquareFixedCoordinateSolution_ext hC₀ P Q
  subst Q
  rfl

/-- On every finite family in one fixed basis, passing to complete coordinate
codes preserves cardinality exactly. -/
theorem card_image_shiftedSquareCoordinateCode_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ}
    (S : Finset (ShiftedSquareEncodedFixedBasisSolution a basis t c)) :
    (S.image ShiftedSquareEncodedFixedBasisSolution.code).card = S.card :=
  Finset.card_image_of_injective S
    ShiftedSquareEncodedFixedBasisSolution.code_injective

/-- Any supplied finite container of complete codes bounds a finite family of
fixed-basis shifted-square solutions. -/
theorem card_shiftedSquareEncodedFixedBasisSolution_le_of_codes_subset
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ}
    (S : Finset (ShiftedSquareEncodedFixedBasisSolution a basis t c))
    (T : Finset ShiftedSquareCoordinateCode)
    (hT : S.image ShiftedSquareEncodedFixedBasisSolution.code ⊆ T) :
    S.card ≤ T.card := by
  rw [← card_image_shiftedSquareCoordinateCode_eq S]
  exact Finset.card_le_card hT

end

end PellPaper
