import Pell.NumberFieldIdealNormFibreTransport
import Pell.QuadraticOrderPellFundamentalUnitModel
import Pell.RealQuadraticNumberFieldFundamentalPresentation
import Pell.ShiftedSquareSurfaceForm

/-!
# Fundamental-unit transport from a square-multiple quadratic radicand

For a squarefree natural number `w > 1`, its positive fundamental index is
`w` in residue class one modulo four and `4 * w` otherwise.  Rescaling the
quadratic generator first removes a positive square factor `s^2`; the
squarefree-radicand presentation then gives an explicit rational-algebra
equivalence with the quadratic field at that fundamental index.

Restricting this equivalence to the rings of integers transports every source
unit to the target unit group.  The concrete fundamental-unit model at the
positive fundamental index then writes the transported unit as a signed
integral power of its oriented generator.  This is the field-transport part
of the unit-orbit argument in the manuscript; no archimedean height
estimate is asserted here.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- The positive fundamental index associated with a squarefree radicand. -/
def squarefreeQuadraticFundamentalIndex (w : ℕ) : ℕ :=
  if w % 4 = 1 then w else 4 * w

/-- The fundamental index of a squarefree radicand greater than one is a
positive fundamental discriminant. -/
theorem squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
    (w : ℕ) (hw : Squarefree w) (hwone : 1 < w) :
    PositiveFundamentalDiscriminant (squarefreeQuadraticFundamentalIndex w) := by
  simpa only [squarefreeQuadraticFundamentalIndex] using
    positiveFundamentalDiscriminant_squarefree_index w hwone hw

/-- Removing the positive square factor and then changing to the positive
fundamental index gives an explicit equivalence of rational quadratic
algebras. -/
noncomputable def squarefreeMulSqFundamentalAlgEquiv
    (w s : ℕ) (hs : 0 < s) :
    rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ) ≃ₐ[ℚ]
      rationalQuadraticAlgebra
        ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ) :=
  let t : ℚ := if w % 4 = 1 then 1 else 2
  let c : ℚ := (s : ℚ) / t
  have ht : t ≠ 0 := by
    dsimp only [t]
    split <;> norm_num
  have hc : c ≠ 0 := div_ne_zero (by exact_mod_cast hs.ne') ht
  have hradicand :
      (w : ℚ) * (s : ℚ) ^ 2 =
        (squarefreeQuadraticFundamentalIndex w : ℚ) * c ^ 2 := by
    dsimp only [c, t, squarefreeQuadraticFundamentalIndex]
    by_cases hmod : w % 4 = 1
    · simp [hmod]
    · simp only [if_neg hmod]
      push_cast
      ring
  {
    toFun z := ⟨z.re, c * z.im⟩
    invFun z := ⟨z.re, z.im / c⟩
    left_inv z := by
      ext <;> simp
      field_simp [hc]
    right_inv z := by
      ext <;> simp
      field_simp [hc]
    map_mul' z z' := by
      ext <;> simp
      · rw [hradicand]
        ring
      · ring
    map_add' z z' := by
      ext <;> simp
      ring
    commutes' q := by
      ext <;> simp
  }

local instance squarefreeFundamentalUnitTransport_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The equivalence on rings of integers induced by removal of the square
factor and passage to the positive fundamental index.  The two field
hypotheses are listed explicitly so this reusable map has no hidden choice of
squarefreeness witnesses. -/
noncomputable def squarefreeMulSqFundamentalRingOfIntegersEquiv
    (w s : ℕ) (hs : 0 < s)
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ))]
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ))] :
    NumberField.RingOfIntegers
        (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ)) ≃+*
      NumberField.RingOfIntegers
        (rationalQuadraticAlgebra
          ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ)) :=
  ringOfIntegersRingEquivOfAlgEquiv _ _
    (squarefreeMulSqFundamentalAlgEquiv w s hs)

/-- Every unit from the square-multiple quadratic presentation maps to a
signed integral power of the oriented concrete fundamental unit at the
positive fundamental index. -/
theorem exists_map_eq_signed_zpow_concreteFundamentalUnit
    (w s : ℕ) (hw : Squarefree w) (hwone : 1 < w) (hs : 0 < s) :
    let Delta : ℤ := ((w * s ^ 2 : ℕ) : ℤ)
    let D : ℕ := squarefreeQuadraticFundamentalIndex w
    let hD : PositiveFundamentalDiscriminant D :=
      squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
        w hw hwone
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot Delta) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare Delta (by
        dsimp only [Delta]
        simpa only [Int.isSquare_natCast_iff] using
          not_isSquare_squarefree_mul_sq hw hwone hs)⟩
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
        hD⟩
    ∀ u : (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra Delta))ˣ,
      ∃ n : ℤ,
        Units.map
            (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs).toMonoidHom u =
          (concreteFundamentalUnitRealModel D hD).etaUnit ^ n ∨
        Units.map
            (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs).toMonoidHom u =
          -((concreteFundamentalUnitRealModel D hD).etaUnit ^ n) := by
  let Delta : ℤ := ((w * s ^ 2 : ℕ) : ℤ)
  let D : ℕ := squarefreeQuadraticFundamentalIndex w
  let hD : PositiveFundamentalDiscriminant D :=
    squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
      w hw hwone
  have hDeltaNotSquare : ¬ IsSquare Delta := by
    dsimp only [Delta]
    simpa only [Int.isSquare_natCast_iff] using
      not_isSquare_squarefree_mul_sq hw hwone hs
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot Delta) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare Delta
      hDeltaNotSquare⟩
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
      hD⟩
  dsimp only
  intro u
  exact (concreteFundamentalUnitRealModel D hD).signed_zpow
    (Units.map
      (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs).toMonoidHom u)

end
end PellPaper
