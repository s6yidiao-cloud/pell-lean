import Pell.PrimitiveSlopeFibre
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Recovering raw positive primitive targets from slope keys

The raw target vector is `(v,u)`, whereas actual tuples have the nested
coordinate order `(d,e,u,v)`. Coprimality fixes the integral scale, and
positive `u` fixes the sign of the primitive slope representative. Thus
the literal source projection `(d,e)` is injective on any one raw slope
fibre of a finite family. No norm, height, or counting premise is required.
This is a raw-coordinate statement, not a supplied reduced-basis recovery.
-/

namespace PellPaper

/-- Equal slopes of primitive raw target vectors `(v,u)` with positive `u`
determine both natural target coordinates. The numerator `v` may be zero. -/
theorem raw_target_eq_of_primitive_positive_slope_eq
    (u v u' v' : ℕ)
    (hu : 0 < u) (hu' : 0 < u')
    (hcop : u.Coprime v) (hcop' : u'.Coprime v')
    (hslope :
      integralBinarySlope ![(v : ℤ), (u : ℤ)] =
      integralBinarySlope ![(v' : ℤ), (u' : ℤ)]) :
    u = u' ∧ v = v' := by
  rcases primitive_eq_or_neg_of_integralBinarySlope_eq
      ![(v : ℤ), (u : ℤ)] ![(v' : ℤ), (u' : ℤ)]
      (by simpa using hcop.symm.isCoprime)
      (by simpa using hcop'.symm.isCoprime) hslope with heq | heq
  · have huZ : (u' : ℤ) = (u : ℤ) := by simpa using congrFun heq (1 : Fin 2)
    have hvZ : (v' : ℤ) = (v : ℤ) := by simpa using congrFun heq (0 : Fin 2)
    exact ⟨by exact_mod_cast huZ.symm, by exact_mod_cast hvZ.symm⟩
  · have huZ : (u' : ℤ) = -(u : ℤ) := by simpa using congrFun heq (1 : Fin 2)
    have hupos : (0 : ℤ) < u := by exact_mod_cast hu
    have hu'pos : (0 : ℤ) < u' := by exact_mod_cast hu'
    omega

/-- On a literal raw slope fibre of positive primitive targets, the raw
target is fixed and the source-pair projection is injective. Empty fibres
are allowed, without choosing a representative or any source primitivity. -/
theorem fixed_raw_target_and_sourcePair_injective_on_slope
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hupos : ∀ q ∈ S, 0 < q.2.2.1)
    (hcop : ∀ q ∈ S, q.2.2.1.Coprime q.2.2.2)
    (r : Option ℚ) :
    let F := S.filter fun q =>
      integralBinarySlope ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] = r
    (∀ p ∈ F, ∀ q ∈ F,
      p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2) ∧
    Set.InjOn (fun q : ℕ × ℕ × ℕ × ℕ => (q.1, q.2.1))
      (↑F : Set (ℕ × ℕ × ℕ × ℕ)) := by
  classical
  let F := S.filter fun q =>
    integralBinarySlope ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] = r
  change (∀ p ∈ F, ∀ q ∈ F,
      p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2) ∧
    Set.InjOn (fun q : ℕ × ℕ × ℕ × ℕ => (q.1, q.2.1))
      (↑F : Set (ℕ × ℕ × ℕ × ℕ))
  have hfixed : ∀ p ∈ F, ∀ q ∈ F,
      p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2 := by
    intro p hp q hq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    exact raw_target_eq_of_primitive_positive_slope_eq
      p.2.2.1 p.2.2.2 q.2.2.1 q.2.2.2
      (hupos p hp'.1) (hupos q hq'.1) (hcop p hp'.1) (hcop q hq'.1)
      (hp'.2.trans hq'.2.symm)
  refine ⟨hfixed, ?_⟩
  intro p hp q hq hpq
  obtain ⟨hu, hv⟩ := hfixed p hp q hq
  apply Prod.ext
  · exact congrArg (fun w : ℕ × ℕ => w.1) hpq
  · apply Prod.ext
    · exact congrArg (fun w : ℕ × ℕ => w.2) hpq
    · exact Prod.ext hu hv

end PellPaper
