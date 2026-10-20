import Pell.NumberFieldIdealNormFibreTransport
import Pell.RealQuadraticNumberFieldFundamentalPresentation
import Pell.ShiftedSquareSurfaceForm

/-!
# Ideal-norm divisor bound at a squarefree quadratic kernel

If `w` is squarefree and greater than one and `s` is positive, rescaling the
quadratic generator identifies `Q(sqrt (w*s^2))` with `Q(sqrt w)`.  The latter
has positive fundamental index `w` or `4*w`.  Transporting the already proved
fundamental-discriminant ideal count across these two explicit equivalences
shows that the number of integral ideals of norm `n` is at most `tau(n)`.

This is the exact field shape produced by the fixed-target discriminant data
in the manuscript.  It uses no Weil bound and no asymptotic estimate.
-/

namespace PellPaper

open NumberField

noncomputable section

local instance rationalQuadraticAlgebra_squarefreeIdealBound_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The field at the square-multiple radicand `w*s^2` has at most `tau(n)`
integral ideals of every positive norm `n`. -/
theorem squarefree_mul_sq_card_idealNormFibre_le_card_divisors
    (w s n : ℕ) (hw : Squarefree w) (hwone : 1 < w) (hs : 0 < s)
    (hn : n ≠ 0) :
    let Delta : ℤ := ((w * s ^ 2 : ℕ) : ℤ)
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot Delta) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare Delta (by
        dsimp only [Delta]
        simpa only [Int.isSquare_natCast_iff] using
          not_isSquare_squarefree_mul_sq hw hwone hs)⟩
    Nat.card {I : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra Delta)) // Ideal.absNorm I = n} ≤
        n.divisors.card := by
  let Delta : ℤ := ((w * s ^ 2 : ℕ) : ℤ)
  have hDeltaNotSquare : ¬ IsSquare Delta := by
    dsimp only [Delta]
    simpa only [Int.isSquare_natCast_iff] using
      not_isSquare_squarefree_mul_sq hw hwone hs
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have eScale :
      rationalQuadraticAlgebra Delta ≃ₐ[ℚ]
        rationalQuadraticAlgebra (w : ℤ) := by
    change QuadraticAlgebra ℚ ((Delta : ℤ) : ℚ) 0 ≃ₐ[ℚ]
      QuadraticAlgebra ℚ ((w : ℤ) : ℚ) 0
    have hcast : ((Delta : ℤ) : ℚ) = (w : ℚ) * (s : ℚ) ^ 2 := by
      dsimp only [Delta]
      push_cast
      ring
    rw [hcast]
    exact quadraticAlgebraScaleAlgEquiv (w : ℚ) (s : ℚ) hsQ
  let D : ℕ := if w % 4 = 1 then w else 4 * w
  have hD : PositiveFundamentalDiscriminant D := by
    dsimp only [D]
    exact positiveFundamentalDiscriminant_squarefree_index w hwone hw
  obtain ⟨eFund⟩ := squarefree_radicand_fundamental_index_algEquiv w
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot Delta) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare Delta hDeltaNotSquare⟩
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have e : rationalQuadraticAlgebra Delta ≃ₐ[ℚ]
      rationalQuadraticAlgebra (D : ℤ) := by
    exact eScale.trans eFund
  exact card_idealNormFibre_le_card_divisors_of_quadraticFundamental_algEquiv
    (rationalQuadraticAlgebra Delta) D hD e n hn

end
end PellPaper
