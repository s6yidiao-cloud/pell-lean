import Pell.RankTwoHermiteSubmodule
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-! Exact index of a triangular rank-two integer lattice. -/

namespace PellPaper

/-- The column map of the two literal Hermite generators. -/
def rankTwoHermiteLinearMap (a b d : ℤ) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  Matrix.toLin' !![a, b; 0, d]

theorem rankTwoHermiteLinearMap_apply (a b d : ℤ) (v : Fin 2 → ℤ) :
    rankTwoHermiteLinearMap a b d v = ![a * v 0 + b * v 1, d * v 1] := by
  simp [rankTwoHermiteLinearMap, Matrix.toLin'_apply, dotProduct,
    Fin.sum_univ_two]

theorem range_rankTwoHermiteLinearMap (a b d : ℤ) :
    (rankTwoHermiteLinearMap a b d).range = rankTwoHermiteSubmodule a b d := by
  ext v
  rw [LinearMap.mem_range, mem_rankTwoHermiteSubmodule_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w 0, w 1, by simp [rankTwoHermiteLinearMap_apply]⟩
  · rintro ⟨x, y, h0, h1⟩
    refine ⟨![x, y], ?_⟩
    rw [rankTwoHermiteLinearMap_apply]
    funext i
    fin_cases i <;> simp_all

theorem rankTwoHermiteLinearMap_injective (a b d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Injective (rankTwoHermiteLinearMap a b d) := by
  intro v w h
  have h1 : v 1 = w 1 := mul_left_cancel₀ hd (by
    simpa [rankTwoHermiteLinearMap_apply] using congr_fun h 1)
  have h0 : v 0 = w 0 := mul_left_cancel₀ ha (by
    have := congr_fun h 0
    simpa [rankTwoHermiteLinearMap_apply, h1] using this)
  funext i
  fin_cases i <;> assumption

theorem index_rankTwoHermiteSubmodule (a b d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) :
    (rankTwoHermiteSubmodule a b d).toAddSubgroup.index = (a * d).natAbs := by
  let f := rankTwoHermiteLinearMap a b d
  let e := LinearEquiv.ofInjective f (rankTwoHermiteLinearMap_injective a b d ha hd)
  have h := Submodule.natAbs_det_equiv f.range e
  have he : f.range.subtype ∘ₗ AddMonoidHom.toIntLinearMap
      (e : (Fin 2 → ℤ) →+ f.range) = f := by
    ext v i
    rfl
  rw [he] at h
  change (LinearMap.det f).natAbs = f.range.toAddSubgroup.index at h
  rw [← range_rankTwoHermiteLinearMap]
  rw [← h]
  simp [f, rankTwoHermiteLinearMap, LinearMap.det_toLin', Matrix.det_fin_two]

theorem index_rankTwoHermiteSubmodule_nat (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (rankTwoHermiteSubmodule a b d).toAddSubgroup.index = a * d := by
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using index_rankTwoHermiteSubmodule (a : ℤ) (b : ℤ) (d : ℤ)
    (by exact_mod_cast Nat.ne_of_gt ha) (by exact_mod_cast Nat.ne_of_gt hd)

end PellPaper
