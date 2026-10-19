import Mathlib.Algebra.Polynomial.Roots

/-!
# A degree bound for finite rational projective zero keys

An affine key `some r` is a root of a nonzero rational polynomial. The
infinity key `none` is permitted only when its coefficient at the stated
homogeneous degree vanishes. It then consumes the strict gap between the
actual affine degree and that stated degree, so the bound is d, not d+1.
This is the finite target-slope part of the manuscript; no bound for
source fibres over those slopes is asserted here.
-/

namespace PellPaper

/-- A finite family of rational zero keys has size at most the homogeneous
degree budget. The nonzero constant and degree-zero cases are included.
No polynomial splitting, squarefreeness, or positive-degree premise is used. -/
theorem card_projective_polynomial_zero_keys_le
    (p : Polynomial ℚ) (d : ℕ) (hp : p ≠ 0) (hdeg : p.natDegree ≤ d)
    (U : Finset (Option ℚ))
    (hU : ∀ u ∈ U, match u with
      | none => p.coeff d = 0
      | some r => p.eval r = 0) :
    U.card ≤ d := by
  classical
  let R := p.roots.toFinset.image some
  have hR : R.card ≤ p.natDegree :=
    Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))
  have hroot (r : ℚ) (hr : some r ∈ U) : some r ∈ R := by
    apply Finset.mem_image.mpr
    exact ⟨r, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hU (some r) hr)), rfl⟩
  by_cases hinfinity : none ∈ U
  · have hgap : p.natDegree < d := by
      by_contra hn
      have heq : p.natDegree = d := Nat.le_antisymm hdeg (Nat.le_of_not_gt hn)
      have hcoeff : p.coeff d = 0 := hU none hinfinity
      rw [← heq, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at hcoeff
      exact hp hcoeff
    have hsubset : U ⊆ insert none R := by
      intro u hu
      cases u with
      | none => exact Finset.mem_insert_self _ _
      | some r => exact Finset.mem_insert_of_mem (hroot r hu)
    calc
      U.card ≤ (insert none R).card := Finset.card_le_card hsubset
      _ ≤ R.card + 1 := Finset.card_insert_le _ _
      _ ≤ p.natDegree + 1 := Nat.add_le_add_right hR 1
      _ ≤ d := hgap
  · have hsubset : U ⊆ R := by
      intro u hu
      cases u with
      | none => exact (hinfinity hu).elim
      | some r => exact hroot r hu
    exact (Finset.card_le_card hsubset).trans (hR.trans hdeg)

end PellPaper
