import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic

/-!
# Zero frequency for homogeneous forms of odd degree

The complete quadratic-character sum of a homogeneous binary form of odd degree
vanishes over every odd prime field. This is the zero-frequency assertion in
`main.tex`, in the proof of the anisotropic square-sieve lemma. No squarefreeness,
good-reduction, or bound on the degree relative to the prime is needed here.
-/

namespace PellPaper

open scoped BigOperators

private theorem eval_scale_of_isHomogeneous
    {R σ : Type*} [CommSemiring R] [Fintype σ]
    (J : MvPolynomial σ R) (j : ℕ) (hJ : J.IsHomogeneous j)
    (t : R) (v : σ → R) :
    MvPolynomial.eval (fun i => t * v i) J =
      t ^ j * MvPolynomial.eval v J := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : (∑ i, d i) = j := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hJ (MvPolynomial.mem_support_iff.mp hd)
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ac_rfl

/-- The actual complete quadratic-character sum of an odd-degree homogeneous
binary form is zero over an odd prime field. -/
theorem sum_quadraticChar_eval_binary_eq_zero_of_homogeneous_odd
    (p j : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (J : MvPolynomial (Fin 2) (ZMod p))
    (hJ : J.IsHomogeneous j) (hj : Odd j) :
    (∑ x : ZMod p, ∑ y : ZMod p,
      quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J)) = 0 := by
  classical
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p)
    (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hscale (x y : ZMod p) :
      quadraticChar (ZMod p) (MvPolynomial.eval ![(a : ZMod p) * x, a * y] J) =
        -quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J) := by
    have hv : ![(a : ZMod p) * x, a * y] =
        fun i => (a : ZMod p) * ![x, y] i := by
      ext i
      fin_cases i <;> rfl
    rw [hv, eval_scale_of_isHomogeneous J j hJ, map_mul, map_pow, ha,
      hj.neg_one_pow, neg_one_mul]
  have hperm :
      (∑ x : ZMod p, ∑ y : ZMod p,
        quadraticChar (ZMod p)
          (MvPolynomial.eval ![(a : ZMod p) * x, a * y] J)) =
      (∑ x : ZMod p, ∑ y : ZMod p,
        quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J)) := by
    calc
      _ = ∑ x : ZMod p, ∑ y : ZMod p,
          quadraticChar (ZMod p) (MvPolynomial.eval ![x, a * y] J) :=
        (mulLeft_bijective₀ (a : ZMod p) a.ne_zero).sum_comp
          (fun x => ∑ y : ZMod p,
            quadraticChar (ZMod p) (MvPolynomial.eval ![x, a * y] J))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        exact (mulLeft_bijective₀ (a : ZMod p) a.ne_zero).sum_comp
          (fun y => quadraticChar (ZMod p) (MvPolynomial.eval ![x, y] J))
  simp_rw [hscale, Finset.sum_neg_distrib] at hperm
  omega

/-- The integer-coefficient specialization uses literal least nonnegative
residue representatives and the actual Legendre symbol. -/
theorem sum_legendreSym_eval_binary_eq_zero_of_homogeneous_odd
    (p j : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (J : MvPolynomial (Fin 2) ℤ)
    (hJ : J.IsHomogeneous j) (hj : Odd j) :
    (∑ x : ZMod p, ∑ y : ZMod p,
      legendreSym p (MvPolynomial.eval ![(x.val : ℤ), (y.val : ℤ)] J)) = 0 := by
  have h := sum_quadraticChar_eval_binary_eq_zero_of_homogeneous_odd p j hp
    (J.map (Int.castRingHom (ZMod p))) (hJ.map (Int.castRingHom (ZMod p))) hj
  convert h using 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  unfold legendreSym
  congr 1
  rw [MvPolynomial.eval_map]
  change (Int.castRingHom (ZMod p)) (MvPolynomial.eval ![(x.val : ℤ), (y.val : ℤ)] J) = _
  rw [MvPolynomial.eval₂_comp]
  congr 1
  ext i
  fin_cases i <;> simp

end PellPaper
