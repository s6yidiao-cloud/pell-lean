import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A rational square-root presentation of every quadratic number field

For any actual number field of rational degree two, the quadratic-extension
instances make the extension cyclic Galois.  Kummer's existing generator
theorem applies because `-1` is a primitive second root of unity in `ℚ`.
It supplies a nonrational generator whose square is rational.

The radicand has no rational square root, and the resulting substitution
map gives an actual rational algebra equivalence with
`QuadraticAlgebra ℚ a 0`.  No realness, positivity, integral radicand, or
fundamental-discriminant parametrization is asserted by this slice.
-/

namespace PellPaper

noncomputable section

/-- Rational degree two alone supplies a nonrational square-root generator
of the whole field; cyclicity and the generator are not caller inputs. -/
theorem exists_quadraticNumberField_square_generator (K : Type*)
    [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ (a : ℚ) (x : K), x ^ 2 = algebraMap ℚ K a ∧
      x ∉ Set.range (algebraMap ℚ K) ∧
        IntermediateField.adjoin ℚ ({x} : Set K) = ⊤ := by
  let _ : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  have hroots : (primitiveRoots (Module.finrank ℚ K) ℚ).Nonempty := by
    rw [hK]
    refine ⟨-1, (mem_primitiveRoots (by decide : 0 < 2)).mpr ?_⟩
    exact IsPrimitiveRoot.neg_one 0 (by decide)
  obtain ⟨x, ⟨a, ha⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic ℚ K hroots
  have hx : x ∉ Set.range (algebraMap ℚ K) := by
    intro hx
    have hbot : IntermediateField.adjoin ℚ ({x} : Set K) = ⊥ :=
      IntermediateField.adjoin_simple_eq_bot_iff.mpr (IntermediateField.mem_bot.mpr hx)
    have hdim := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp (hbot.symm.trans hgen)
    rw [hK] at hdim
    norm_num at hdim
  exact ⟨a, x, by simpa only [hK] using ha.symm, hx, hgen⟩

/-- Every quadratic number field is actually rational-algebra-equivalent
to a concrete quadratic algebra with a nonsquare rational radicand. -/
theorem exists_quadraticNumberField_quadraticAlgebra_algEquiv (K : Type*)
    [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ a : ℚ, (∀ r : ℚ, r ^ 2 ≠ a) ∧
      Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ a 0) := by
  obtain ⟨a, x, hsq, hx, _⟩ := exists_quadraticNumberField_square_generator K hK
  have ha : ∀ r : ℚ, r ^ 2 ≠ a := by
    intro r hr
    have heq : x ^ 2 = (algebraMap ℚ K r) ^ 2 := by
      rw [hsq, ← map_pow, hr]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · exact hx ⟨r, h.symm⟩
    · exact hx ⟨-r, by rw [map_neg]; exact h.symm⟩
  let _ : Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r) := ⟨by simpa using ha⟩
  let f : QuadraticAlgebra ℚ a 0 →ₐ[ℚ] K := QuadraticAlgebra.lift
    ⟨x, by
      simpa only [pow_two, zero_smul, add_zero, Algebra.smul_def, mul_one,
        map_zero, zero_mul] using hsq⟩
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (show Module.finrank ℚ (QuadraticAlgebra ℚ a 0) = Module.finrank ℚ K by
        rw [QuadraticAlgebra.finrank_eq_two, hK])).mp hinj
  exact ⟨a, ha, ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩⟩

end
end PellPaper
