import Pell.QuadraticIdealNormalizedNormDiscriminant

/-!
# Orienting an actual ideal basis

An integer basis generates the same ideal over the ring of integers.  At a
positive fundamental discriminant, the determinant-index identity makes its
rational coordinate wedge equal to plus or minus half the ideal norm.
Swapping the basis vectors chooses the negative sign, matching the attached
form-ideal basis convention `a, -theta`.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_normalizedNormOrientation_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- An actual two-element integer ideal basis also generates the ideal over
the full ring of integers. -/
theorem quadraticIdealIntegerBasis_span_pair (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (bI : Module.Basis (Fin 2) ℤ I) : Ideal.span {(bI 0).1, (bI 1).1} = I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact (bI 0).2
    · exact (bI 1).2
  · intro z hz
    have hsum := congrArg Subtype.val (bI.sum_repr ⟨z, hz⟩)
    simp only [Fin.sum_univ_two] at hsum
    change (bI.repr ⟨z, hz⟩ 0) • (bI 0).1 +
      (bI.repr ⟨z, hz⟩ 1) • (bI 1).1 = z at hsum
    rw [← hsum, zsmul_eq_mul, zsmul_eq_mul]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

private theorem algebraTrace_cast_eq_coordinates (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ((Algebra.trace ℤ _ z : ℤ) : ℚ) = 2 * (z : rationalQuadraticAlgebra D).re := by
  change (algebraMap ℤ ℚ) (Algebra.trace ℤ _ z) = _
  rw [← Algebra.intTrace_eq_trace ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  rw [Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ)
    (L := rationalQuadraticAlgebra D)
    (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  exact rationalQuadraticAlgebra_trace_apply D (z : rationalQuadraticAlgebra D)

private theorem integerPair_discriminant_cast (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ((Algebra.discr ℤ ![x, y] : ℤ) : ℚ) =
      4 * (D : ℚ) * ((x : rationalQuadraticAlgebra D).re *
        (y : rationalQuadraticAlgebra D).im -
          (x : rationalQuadraticAlgebra D).im * (y : rationalQuadraticAlgebra D).re) ^ 2 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change ((Algebra.trace ℤ _ (x * x) * Algebra.trace ℤ _ (y * y) -
    Algebra.trace ℤ _ (x * y) * Algebra.trace ℤ _ (y * x) : ℤ) : ℚ) = _
  simp only [Int.cast_sub, Int.cast_mul, algebraTrace_cast_eq_coordinates]
  change 2 * ((x : rationalQuadraticAlgebra D) * x).re *
      (2 * ((y : rationalQuadraticAlgebra D) * y).re) -
    2 * ((x : rationalQuadraticAlgebra D) * y).re *
      (2 * ((y : rationalQuadraticAlgebra D) * x).re) = _
  simp
  ring

/-- The doubled rational coordinate wedge of an actual ideal basis has
square equal to the square of the absolute ideal norm. -/
theorem quadraticIdealIntegerBasis_wedge_sq (D : ℕ)
    (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
      (bI : Module.Basis (Fin 2) ℤ I),
      (2 * (((bI 0).1 : rationalQuadraticAlgebra (D : ℤ)).re *
        ((bI 1).1 : rationalQuadraticAlgebra (D : ℤ)).im -
          ((bI 0).1 : rationalQuadraticAlgebra (D : ℤ)).im *
            ((bI 1).1 : rationalQuadraticAlgebra (D : ℤ)).re)) ^ 2 = (I.absNorm : ℚ) ^ 2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro I bI
  have hfield : NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) = (D : ℤ) :=
    rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD
  have hdisc := congrArg (fun n : ℤ => (n : ℚ))
    (quadraticIdealIntegerBasis_discriminant (D : ℤ) I bI)
  have hvec : ![(bI 0).1, (bI 1).1] = fun i => (bI i).1 := by
    funext i
    fin_cases i <;> rfl
  rw [← hvec, integerPair_discriminant_cast, hfield] at hdisc
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] at hdisc
  have hD0 : (D : ℚ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 from by have := hD.1; omega)
  apply mul_left_cancel₀ hD0
  nlinarith [hdisc]

/-- Every nonzero actual ideal admits an integer basis with the orientation
needed by the normalized norm form's attachment convention. -/
theorem exists_quadraticIdealIntegerBasis_negative_wedge (D : ℕ)
    (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
      (_hI : I ≠ ⊥), ∃ bI : Module.Basis (Fin 2) ℤ I,
      2 * (((bI 0).1 : rationalQuadraticAlgebra (D : ℤ)).re *
        ((bI 1).1 : rationalQuadraticAlgebra (D : ℤ)).im -
          ((bI 0).1 : rationalQuadraticAlgebra (D : ℤ)).im *
            ((bI 1).1 : rationalQuadraticAlgebra (D : ℤ)).re) = -(I.absNorm : ℚ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro I hI
  let b := quadraticIdealIntegerBasis (D : ℤ) I hI
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (quadraticIdealIntegerBasis_wedge_sq D hD I b)
    with hpos | hneg
  · refine ⟨b.reindex (Equiv.swap 0 1), ?_⟩
    simp only [Module.Basis.coe_reindex, Function.comp_apply, Equiv.symm_swap,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    nlinarith [hpos]
  · exact ⟨b, hneg⟩

end
end IntegralBinaryQuadraticForm
end PellPaper
