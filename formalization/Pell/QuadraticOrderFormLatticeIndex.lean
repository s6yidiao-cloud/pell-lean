import Pell.QuadraticFormIdealBasis
import Pell.QuadraticIdealNormalizedNormDiscriminant
import Pell.RealQuadraticNumberFieldPositiveRadicand
import Mathlib.Data.Int.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# The conductor index of the raw lattice attached to a quadratic form

For a primitive form of discriminant `D₀ * f²`, the two literal vectors
`a` and `-theta` span a sublattice of index `f` inside the actual maximal-order
ideal attached to the form.  The proof compares discriminants: the raw basis
has discriminant `a² D₀ f²`, while an integer basis of the ambient ideal has
discriminant `|a|² D₀`.

This does not construct a nonmaximal quadratic order or assert that the raw
lattice is an invertible ideal of such an order.
-/

namespace PellPaper

noncomputable section

/-- Multiplying a positive fundamental radicand by a nonzero integer square
does not create a rational square root. -/
theorem rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ)) := by
  intro r hr
  have hbase := rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD₀
  have hfq : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  have hr' : r ^ 2 = ((D₀ : ℤ) : ℚ) * (f : ℚ) ^ 2 := by
    norm_num only [add_zero, zero_mul] at hr ⊢
    exact_mod_cast hr
  apply hbase (r / (f : ℚ))
  simp only [add_zero, zero_mul]
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hfq)]
  rw [hr']

local instance rationalQuadraticAlgebra_formLatticeIndex_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The concrete quadratic field with radicand `D₀ f²` has actual field
discriminant `D₀`. -/
theorem rationalQuadraticAlgebraFieldDiscriminant_nat_mul_sq
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f) :
    let _ : Fact
        (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
    NumberField.discr (rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ))) =
      (D₀ : ℤ) := by
  let _ : Fact
      (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D₀ : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD₀⟩
  have hfq : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  let e : rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ)) ≃ₐ[ℚ]
      rationalQuadraticAlgebra (D₀ : ℤ) := by
    refine
      { toFun := fun z => ⟨z.re, (f : ℚ) * z.im⟩
        invFun := fun z => ⟨z.re, z.im / (f : ℚ)⟩
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_
        map_add' := ?_
        commutes' := ?_ }
    · intro z
      ext <;> simp
      field_simp [hfq]
    · intro z
      ext <;> simp
      field_simp [hfq]
    · intro z w
      ext <;> simp <;> ring
    · intro z w
      ext <;> simp
      ring
    · intro r
      ext <;> simp
  calc
    NumberField.discr (rationalQuadraticAlgebra (((D₀ * f ^ 2 : ℕ) : ℤ))) =
        NumberField.discr (rationalQuadraticAlgebra (D₀ : ℤ)) :=
      NumberField.discr_eq_discr_of_algEquiv _ e
    _ = (D₀ : ℤ) :=
      rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D₀ hD₀

namespace IntegralBinaryQuadraticForm

/-- A form of nonsquare discriminant has nonzero leading coefficient. -/
theorem leadingCoefficient_ne_zero_of_noRationalRoot (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] : Q.a ≠ 0 := by
  intro ha
  have hroot := Fact.out (p := rationalQuadraticAlgebraNoRationalRoot D) (Q.b : ℚ)
  apply hroot
  exact_mod_cast (by simpa [discriminant, ha] using hQ)

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

/-- The two literal form vectors `a` and `-theta` have discriminant `a² D`. -/
theorem formIdealIntegerVectors_discriminant (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Algebra.discr ℤ ![formIdealVector D Q hQ 1 0,
      formIdealVector D Q hQ 0 1] = Q.a ^ 2 * D := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change Algebra.trace ℤ _
      (formIdealVector D Q hQ 1 0 * formIdealVector D Q hQ 1 0) *
        Algebra.trace ℤ _
          (formIdealVector D Q hQ 0 1 * formIdealVector D Q hQ 0 1) -
      Algebra.trace ℤ _
          (formIdealVector D Q hQ 1 0 * formIdealVector D Q hQ 0 1) *
        Algebra.trace ℤ _
          (formIdealVector D Q hQ 0 1 * formIdealVector D Q hQ 1 0) = _
  apply (Int.cast_injective (α := ℚ))
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, map_mul,
    algebraTrace_cast_eq_coordinates]
  change 2 * ((formIdealVector D Q hQ 1 0 : rationalQuadraticAlgebra D) *
      formIdealVector D Q hQ 1 0).re *
        (2 * ((formIdealVector D Q hQ 0 1 : rationalQuadraticAlgebra D) *
          formIdealVector D Q hQ 0 1).re) -
      2 * ((formIdealVector D Q hQ 1 0 : rationalQuadraticAlgebra D) *
        formIdealVector D Q hQ 0 1).re *
        (2 * ((formIdealVector D Q hQ 0 1 : rationalQuadraticAlgebra D) *
          formIdealVector D Q hQ 1 0).re) = (Q.a : ℚ) ^ 2 * (D : ℚ)
  have hdisc : (Q.b : ℚ) ^ 2 - 4 * Q.a * Q.c = D := by exact_mod_cast hQ
  simp only [coe_formIdealVector]
  simp
  have hmul := congrArg (fun z : ℚ => (Q.a : ℚ) ^ 2 * z) hdisc
  ring_nf at hmul ⊢

/-- For a primitive form of discriminant `D₀ f²`, its literal two-vector
lattice has index exactly `f` in the actual attached maximal-order ideal. -/
theorem formAssociatedIdealIntegerLinearMap_range_index_eq_conductor
    (D₀ f : ℕ) (hD₀ : PositiveFundamentalDiscriminant D₀) (hf : 0 < f)
    (Q : PrimitiveBinaryQuadraticForms (((D₀ * f ^ 2 : ℕ) : ℤ))) :
    let _ : Fact
        (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
    (LinearMap.range
      (formAssociatedIdealIntegerLinearMap (((D₀ * f ^ 2 : ℕ) : ℤ)) Q.1 Q.2.2)).toAddSubgroup.index =
        f := by
  let _ : Fact
      (rationalQuadraticAlgebraNoRationalRoot (((D₀ * f ^ 2 : ℕ) : ℤ))) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_nat_mul_sq D₀ f hD₀ hf⟩
  dsimp only
  let D : ℤ := ((D₀ * f ^ 2 : ℕ) : ℤ)
  let I := formAssociatedIdeal D Q.1 Q.2.2
  let g := formAssociatedIdealIntegerLinearMap D Q.1 Q.2.2
  have ha : Q.1.a ≠ 0 := leadingCoefficient_ne_zero_of_noRationalRoot D Q.1 Q.2.2
  have hg : Function.Injective g :=
    formAssociatedIdealIntegerLinearMap_injective D Q.1 Q.2.2 ha
  have hI : I ≠ ⊥ := formAssociatedIdeal_ne_bot_of_a_ne_zero D Q.1 Q.2.2 ha
  let L := LinearMap.range g
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] L := LinearEquiv.ofInjective g hg
  let bL : Module.Basis (Fin 2) ℤ L := (Pi.basisFun ℤ (Fin 2)).map e
  let bI : Module.Basis (Fin 2) ℤ I := quadraticIdealIntegerBasis D I hI
  rw [AddSubgroup.index_eq_natAbs_det bI L.toAddSubgroup bL]
  let M : Matrix (Fin 2) (Fin 2) ℤ := bI.toMatrix (fun i => (bL i : I))
  have hchange := Algebra.discr_of_matrix_vecMul
    (fun i : Fin 2 => ((bI i).1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) M
  have hvec : Matrix.vecMul
      (fun i : Fin 2 => ((bI i).1 :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
      (M.map (algebraMap ℤ
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))) =
      fun i : Fin 2 => ((bL i : I).1 :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) := by
    funext j
    have hj := bI.sum_toMatrix_smul_self (fun i => (bL i : I)) j
    have hj' := congrArg Subtype.val hj
    change (∑ i : Fin 2, (M i j) •
      ((bI i).1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) =
        ((bL j : I).1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) at hj'
    change (∑ i : Fin 2,
      ((bI i).1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        (M i j : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) =
      ((bL j : I).1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    calc
      _ = ∑ i : Fin 2,
          (M i j : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
            ((bI i).1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
      _ = _ := by simpa only [zsmul_eq_mul] using hj'
  rw [hvec] at hchange
  have hbL_apply (i : Fin 2) : ((bL i : L) : I) = g (Pi.single i 1) := by
    change ((e ((Pi.basisFun ℤ (Fin 2)) i) : L) : I) = g (Pi.single i 1)
    rw [Pi.basisFun_apply]
    exact LinearEquiv.ofInjective_apply g _
  have hbLvec :
      (fun i : Fin 2 => ((bL i : I).1 :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) =
      ![formIdealVector D Q.1 Q.2.2 1 0,
        formIdealVector D Q.1 Q.2.2 0 1] := by
    funext i
    rw [show ((bL i : L) : I) = g (Pi.single i 1) from hbL_apply i]
    change formIdealVector D Q.1 Q.2.2 ((Pi.single i 1 : Fin 2 → ℤ) 0)
      ((Pi.single i 1 : Fin 2 → ℤ) 1) = _
    fin_cases i <;> simp
  rw [hbLvec, formIdealIntegerVectors_discriminant] at hchange
  rw [quadraticIdealIntegerBasis_discriminant] at hchange
  rw [absNorm_formAssociatedIdeal_eq_natAbs D Q.1 Q.2.2 Q.2.1] at hchange
  have hfield : NumberField.discr (rationalQuadraticAlgebra D) = (D₀ : ℤ) := by
    dsimp only [D]
    exact rationalQuadraticAlgebraFieldDiscriminant_nat_mul_sq D₀ f hD₀ hf
  rw [hfield, Int.natCast_natAbs, sq_abs] at hchange
  have hD₀gt : 1 < D₀ := hD₀.1
  have hD₀nat : D₀ ≠ 0 := by omega
  have hD₀ : (D₀ : ℤ) ≠ 0 := by exact_mod_cast hD₀nat
  have hfactor : Q.1.a ^ 2 * (D₀ : ℤ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha) hD₀
  have hdet : M.det ^ 2 = (f : ℤ) ^ 2 := by
    apply mul_left_cancel₀ hfactor
    calc
      (Q.1.a ^ 2 * (D₀ : ℤ)) * M.det ^ 2 =
          M.det ^ 2 * (Q.1.a ^ 2 * (D₀ : ℤ)) := by ring
      _ = Q.1.a ^ 2 * D := hchange.symm
      _ = (Q.1.a ^ 2 * (D₀ : ℤ)) * (f : ℤ) ^ 2 := by
        dsimp only [D]
        push_cast
        ring
  change (M.det).natAbs = f
  have habs : (M.det).natAbs = (f : ℤ).natAbs :=
    (Int.natAbs_eq_iff_sq_eq).mpr hdet
  simpa using habs

end IntegralBinaryQuadraticForm
end
end PellPaper
