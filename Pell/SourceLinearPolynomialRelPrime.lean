import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Tactic

/-!
# Relatively prime coefficients of a literal irreducible source-linear form

Both homogeneous source variables are retained. A common coefficient
divisor factors out of the source polynomial; the remaining source-linear
factor vanishes at the source origin and cannot be a unit. This does not
select the manuscript's irreducible auxiliary factor or identify its
coefficient vector. It is the generic algebraic leaf for that later handoff.
-/

namespace PellPaper

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The literal homogeneous source-linear polynomial with coefficient
components A and B. The coefficient ring may itself be a target polynomial ring. -/
def sourceLinearPolynomial (A B : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C A * MvPolynomial.X 0 + MvPolynomial.C B * MvPolynomial.X 1

/-- Evaluation under an arbitrary coefficient ring homomorphism keeps the
two source coordinates and coefficients in their original order. -/
theorem eval₂_sourceLinearPolynomial (φ : R →+* S) (A B : R) (lambda : Fin 2 → S) :
    MvPolynomial.eval₂ φ lambda (sourceLinearPolynomial A B) =
      φ A * lambda 0 + φ B * lambda 1 := by
  simp [sourceLinearPolynomial]

/-- Irreducibility of the actual two-source-variable polynomial forces
every common coefficient divisor to be a unit. This is relative primeness,
not a multivariate Bezout assertion; no domain or UFD assumption is used. -/
theorem isRelPrime_of_irreducible_sourceLinearPolynomial [Nontrivial R]
    (A B : R) (hF : Irreducible (sourceLinearPolynomial A B)) :
    IsRelPrime A B := by
  intro D hDA hDB
  obtain ⟨a, ha⟩ := hDA
  obtain ⟨b, hb⟩ := hDB
  have hfactor : sourceLinearPolynomial A B =
      MvPolynomial.C D * sourceLinearPolynomial a b := by
    rw [ha, hb]
    simp only [sourceLinearPolynomial, map_mul]
    ring
  rcases hF.isUnit_or_isUnit hfactor with hD | hquotient
  · simpa using hD.map (MvPolynomial.eval (fun _ : Fin 2 => (0 : R)))
  · have hz : IsUnit (0 : R) := by
      simpa [sourceLinearPolynomial] using
        hquotient.map (MvPolynomial.eval (fun _ : Fin 2 => (0 : R)))
    exact False.elim (hz.ne_zero rfl)

end
end PellPaper
