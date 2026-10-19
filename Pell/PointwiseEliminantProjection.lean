import Pell.PrimitiveEliminantProjection
import Pell.BinaryHomogeneousCommonFactor

/-!
# Counting the residual branch from pointwise component nonvanishing

Only component values on actual solutions are needed. Neither multivariate
relative primeness nor irreducibility is a premise of this finite count.
The common-factor zero family is retained in the final two-branch bound.
-/

namespace PellPaper
noncomputable section

/-- The literal finite square-target bound under precisely the pointwise
nonvanishing used by the primitive-source fibre argument. -/
theorem card_primitive_surface_solutions_le_two_mul_squares_of_component_nonvanishing
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A B : MvPolynomial (Fin 2) ℤ)
    (hc : c ≠ 0) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      p.1 0 * MvPolynomial.eval p.2 A + p.1 1 * MvPolynomial.eval p.2 B = 0 ∧
      quadraticLinearFormEval g p.1 p.2 = c)
    (hcomponents : ∀ p ∈ S, MvPolynomial.eval p.2 A ≠ 0 ∨ MvPolynomial.eval p.2 B ≠ 0)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ 2 * (T.filter fun y =>
      IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g c A B)) ∧
        MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0).card := by
  classical
  have hfibre (y : Fin 2 → ℤ) (hy : y ∈ S.image Prod.snd) :
      (S.filter fun p => p.2 = y).card ≤ 2 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have hn := hcomponents p hp
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
    have hv := quadraticLinearEliminant_nonzero_square_of_primitive_source
      g c A B p.1 p.2 (hS p hp).1 hc (hS p hp).2.2.1 (hcomponents p hp)
      (hS p hp).2.2.2
    exact Finset.mem_filter.mpr ⟨hT p hp, hv.1, hv.2.1⟩
  calc
    S.card = ∑ y ∈ S.image Prod.snd, (S.filter fun p => p.2 = y).card :=
      Finset.card_eq_sum_card_image Prod.snd S
    _ ≤ ∑ _ ∈ S.image Prod.snd, 2 := Finset.sum_le_sum hfibre
    _ = 2 * (S.image Prod.snd).card := by simp [mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 2 (Finset.card_le_card himage)
/-- A finite family on the original source-linear zero set splits into
common-target zeros and a residual square-target family. The first family
is counted literally, not silently discarded or assumed to be empty. -/
theorem card_surface_solutions_le_common_factor_zeros_add_twice_squares
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (A₀ B₀ D A B : MvPolynomial (Fin 2) ℤ)
    (hA : A₀ = D * A) (hB : B₀ = D * B) (hc : c ≠ 0)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      p.1 0 * MvPolynomial.eval p.2 A₀ + p.1 1 * MvPolynomial.eval p.2 B₀ = 0 ∧
      quadraticLinearFormEval g p.1 p.2 = c)
    (hcomponents : ∀ p ∈ S, MvPolynomial.eval p.2 D ≠ 0 →
      MvPolynomial.eval p.2 A ≠ 0 ∨ MvPolynomial.eval p.2 B ≠ 0)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ (S.filter fun p => MvPolynomial.eval p.2 D = 0).card +
      2 * (T.filter fun y =>
        IsSquare (MvPolynomial.eval y (quadraticLinearEliminant g c A B)) ∧
          MvPolynomial.eval y (quadraticLinearEliminant g c A B) ≠ 0).card := by
  classical
  let U := S.filter fun p => MvPolynomial.eval p.2 D ≠ 0
  have hU := card_primitive_surface_solutions_le_two_mul_squares_of_component_nonvanishing
    g c A B hc U T (by
      intro p hp
      obtain ⟨hpS, hpD⟩ := Finset.mem_filter.mp hp
      refine ⟨(hS p hpS).1, (hS p hpS).2.1, ?_, (hS p hpS).2.2.2⟩
      exact ((source_linear_zero_iff_common_factor_or_residual
        A₀ B₀ D A B hA hB p.1 p.2).mp (hS p hpS).2.2.1).resolve_left hpD)
    (by
      intro p hp
      obtain ⟨hpS, hpD⟩ := Finset.mem_filter.mp hp
      exact hcomponents p hpS hpD)
    (by intro p hp; exact hT p (Finset.mem_filter.mp hp).1)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun p => MvPolynomial.eval p.2 D = 0)
  change (S.filter fun p => MvPolynomial.eval p.2 D = 0).card + U.card = S.card
    at hpartition
  omega

end
end PellPaper
