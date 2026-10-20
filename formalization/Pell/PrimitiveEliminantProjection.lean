import Pell.BinaryHomogeneousRelPrimeEvaluation
import Pell.PrimitiveSourceLinearFibre
import Pell.TwoLayerEliminant

/-!
# Primitive source-target solutions project to nonzero eliminant squares

Relative primeness of the actual rational binary components discharges their
pointwise nonvanishing. Primitive source fibres have at most two elements,
so a finite family on the exact nonzero surface level is bounded by twice
the actual nonzero square values in its target set. No analytic count is
assumed or concluded here.
-/

namespace PellPaper

noncomputable section

/-- Rational relative primeness replaces the evaluated-component premise in
the literal primitive-source square identity. -/
theorem quadraticLinearEliminant_nonzero_square_of_rat_isRelPrime
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ) (b : ℕ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b)
    (hAB : IsRelPrime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (lambda y : Fin 2 → ℤ) (hlambda : IsCoprime (lambda 0) (lambda 1))
    (hy : IsCoprime (y 0) (y 1)) (hc : c ≠ 0)
    (hlinear : lambda 0 * MvPolynomial.eval y A + lambda 1 * MvPolynomial.eval y B = 0)
    (hlevel : quadraticLinearFormEval g lambda y = c) :
    IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g c A B)) ∧
      MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0 ∧
      quadraticLinearEliminant g c A B ≠ 0 :=
  quadraticLinearEliminant_nonzero_square_of_primitive_source g c A B lambda y
    hlambda hc hlinear
    (eval_ne_zero_or_ne_zero_of_rat_isRelPrime_homogeneous_binary A B b hA hB hAB y hy)
    hlevel

/-- Literal finite solutions project with multiplicity at most two into
the nonzero square values of the actual eliminant. The ambient target set
need not consist of primitive points. Empty families and signed coordinates
are included; there is no unconditional nonzero-eliminant premise. -/
theorem card_primitive_surface_solutions_le_two_mul_eliminant_squares
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ) (b : ℕ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b)
    (hAB : IsRelPrime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (hc : c ≠ 0) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      p.1 0 * MvPolynomial.eval p.2 A + p.1 1 * MvPolynomial.eval p.2 B = 0 ∧
      quadraticLinearFormEval g p.1 p.2 = c)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ 2 * (T.filter fun y =>
      IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g c A B)) ∧
        MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0).card := by
  classical
  have hfibre (y : Fin 2 → ℤ) (hy : y ∈ S.image Prod.snd) :
      (S.filter fun p => p.2 = y).card ≤ 2 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have hn := eval_ne_zero_or_ne_zero_of_rat_isRelPrime_homogeneous_binary
      A B b hA hB hAB p.2 (hS p hp).2.1
    let U := S.filter fun q => q.2 = p.2
    have hinj : Set.InjOn Prod.fst (U : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ))) := by
      intro q hq r hr heq
      exact Prod.ext heq ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm)
    calc
      U.card = (U.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ 2 := by
        apply card_primitive_linear_solutions_le_two (MvPolynomial.eval p.2 A)
          (MvPolynomial.eval p.2 B) hn
        intro lambda hlambda
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hlambda
        have hqS := (Finset.mem_filter.mp hq).1
        have hqy := (Finset.mem_filter.mp hq).2
        exact ⟨(hS q hqS).1, by simpa only [hqy] using (hS q hqS).2.2.1⟩
  have himage : S.image Prod.snd ⊆ T.filter (fun y =>
      IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g c A B)) ∧
        MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0) := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have hv := quadraticLinearEliminant_nonzero_square_of_rat_isRelPrime
      g c A B b hA hB hAB p.1 p.2 (hS p hp).1 (hS p hp).2.1 hc
      (hS p hp).2.2.1 (hS p hp).2.2.2
    exact Finset.mem_filter.mpr ⟨hT p hp, hv.1, hv.2.1⟩
  calc
    S.card = ∑ y ∈ S.image Prod.snd, (S.filter fun p => p.2 = y).card :=
      Finset.card_eq_sum_card_image Prod.snd S
    _ ≤ ∑ _ ∈ S.image Prod.snd, 2 := Finset.sum_le_sum hfibre
    _ = 2 * (S.image Prod.snd).card := by simp [mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 2 (Finset.card_le_card himage)

/-- The finite projection bound for the original two-layer coefficient
vector and original auxiliary-form evaluation, not an unrelated form. -/
theorem card_twoLayer_surface_solutions_le_two_mul_eliminant_squares
    (b : ℕ) (f : twoLayerFormIndex b → ℤ) (g : Fin 3 → Fin 2 → ℤ) (c : ℤ)
    (hAB : IsRelPrime
      ((twoLayerBinaryPolynomial b f 0).map (Int.castRingHom ℚ))
      ((twoLayerBinaryPolynomial b f 1).map (Int.castRingHom ℚ)))
    (hc : c ≠ 0) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      twoLayerFormEval b f ((p.1 0, p.1 1), (p.2 0, p.2 1)) = 0 ∧
      quadraticLinearFormEval g p.1 p.2 = c)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ 2 * (T.filter fun y => IsSquare (MvPolynomial.eval y (twoLayerEliminant b f g c)) ∧
      MvPolynomial.eval y (twoLayerEliminant b f g c) ≠ 0).card := by
  apply card_primitive_surface_solutions_le_two_mul_eliminant_squares g c
    (twoLayerBinaryPolynomial b f 0) (twoLayerBinaryPolynomial b f 1) b
    (twoLayerBinaryPolynomial_isHomogeneous b f 0)
    (twoLayerBinaryPolynomial_isHomogeneous b f 1) hAB hc S T ?_ hT
  intro p hp
  refine ⟨(hS p hp).1, (hS p hp).2.1, ?_, (hS p hp).2.2.2⟩
  have h := (hS p hp).2.2.1
  rw [twoLayerFormEval_eq_binaryPolynomial] at h
  have hy : ![p.2 0, p.2 1] = p.2 := by
    funext i
    fin_cases i <;> rfl
  simpa only [hy] using h

end
end PellPaper
