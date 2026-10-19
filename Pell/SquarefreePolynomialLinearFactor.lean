import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic

/-!
# A squarefree polynomial times a lower-degree factor is not a square

Squarefreeness supplies the radical divisibility step. A hypothetical square
would force the squarefree factor to divide the lower-degree factor, which is
impossible when that factor is nonzero.
-/

namespace PellPaper

/-- A nonzero squarefree polynomial times a nonzero polynomial of strictly
smaller degree cannot be a square. The second factor need not be linear. -/
theorem not_isSquare_squarefree_mul_of_natDegree_lt
    {F : Type*} [Field F] (J L : Polynomial F)
    (hJ : Squarefree J) (hJ0 : J ≠ 0) (hL0 : L ≠ 0)
    (hdeg : L.natDegree < J.natDegree) :
    ¬ IsSquare (J * L) := by
  rintro ⟨g, hg⟩
  have hJgSq : J ∣ g ^ 2 := ⟨L, by simpa only [pow_two] using hg.symm⟩
  have hJg : J ∣ g :=
    (hJ.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hJgSq
  rcases hJg with ⟨k, hk⟩
  apply (Polynomial.not_dvd_of_natDegree_lt hL0 hdeg)
  refine ⟨k * k, ?_⟩
  apply mul_left_cancel₀ hJ0
  calc
    J * L = g * g := hg
    _ = (J * k) * (J * k) := by rw [hk]
    _ = J * (J * (k * k)) := by ring

end PellPaper
