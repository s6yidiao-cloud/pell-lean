import Pell.GeneralBidegreeTaylorFactorialDecay
import Pell.GeneralBidegreeRectangularTaylorFactorization

/-!
# Finite factorial Taylor-tail majorants

The Taylor part of the sheared determinant expansion is indexed by a growing
rectangle of exponent pairs.  The inverse factorials make its positive
coefficient mass uniformly bounded.  This module proves the finite
rectangle and finite ordered-support estimates needed for that eventual
Cauchy--Binet summation.  It does not exchange a limit with a sum or assert
an infinite-series determinant bound.
-/

namespace PellPaper

open scoped BigOperators

/-- The positive factorial-weighted mass of the rectangular Taylor support
through degrees `< N` in each coordinate. -/
noncomputable def rectangularFactorialTaylorMass (u v : ℝ) (N : ℕ) : ℝ :=
  ∑ q : Fin N × Fin N,
    (u ^ q.1.1 / (Nat.factorial q.1.1 : ℝ)) *
      (v ^ q.2.1 / (Nat.factorial q.2.1 : ℝ))

/-- The finite product-indexed factorial mass is exactly the rectangular
partial exponential already used by the Taylor-limit construction. -/
theorem rectangularFactorialTaylorMass_eq_rectangularPartialExp
    (u v : ℝ) (N : ℕ) :
    rectangularFactorialTaylorMass u v N = rectangularPartialExp u v N := by
  unfold rectangularFactorialTaylorMass rectangularPartialExp
  exact sum_finProduct_eq_sum_range N (fun i j =>
    (u ^ i / (Nat.factorial i : ℝ)) * (v ^ j / (Nat.factorial j : ℝ)))

/-- A nonnegative one-variable finite Taylor mass is bounded by its
exponential sum. -/
theorem partialExp_le_exp_of_nonneg (u : ℝ) (N : ℕ) (hu : 0 ≤ u) :
    partialExp u N ≤ Real.exp u := by
  exact Real.sum_le_exp_of_nonneg hu N

/-- The rectangular factorial Taylor mass is uniformly bounded by the
product exponential, equivalently by `exp (u + v)`. -/
theorem rectangularFactorialTaylorMass_le_exp_add
    (u v : ℝ) (N : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    rectangularFactorialTaylorMass u v N ≤ Real.exp (u + v) := by
  rw [rectangularFactorialTaylorMass_eq_rectangularPartialExp,
    rectangularPartialExp_eq_mul_partialExp, Real.exp_add]
  apply mul_le_mul (partialExp_le_exp_of_nonneg u N hu)
    (partialExp_le_exp_of_nonneg v N hv)
  · exact Finset.sum_nonneg fun j _ =>
      div_nonneg (pow_nonneg hv _) (by positivity)
  · exact Real.exp_nonneg _

/-- For a nonnegative finite weight, summing products over injective choices
is bounded by the unrestricted product sum.  The right side is the indicated
power of the one-point mass. -/
theorem sum_injective_prod_le_sum_pow
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : κ → ℝ) (hf : ∀ q, 0 ≤ f q) :
    (∑ p : {p : ι → κ // Function.Injective p}, ∏ i, f (p.1 i)) ≤
      (∑ q : κ, f q) ^ (Fintype.card ι) := by
  calc
    (∑ p : {p : ι → κ // Function.Injective p}, ∏ i, f (p.1 i)) ≤
        ∑ p : ι → κ, ∏ i, f (p i) := by
          classical
          calc
            (∑ p : {p : ι → κ // Function.Injective p}, ∏ i, f (p.1 i)) ≤
                (∑ p : {p : ι → κ // Function.Injective p}, ∏ i, f (p.1 i)) +
                  ∑ p : {p : ι → κ // ¬ Function.Injective p}, ∏ i, f (p.1 i) := by
                    apply le_add_of_nonneg_right
                    apply Finset.sum_nonneg
                    intro p _
                    exact Finset.prod_nonneg fun i _ => hf (p.1 i)
            _ = ∑ p : ι → κ, ∏ i, f (p i) := by
              exact Fintype.sum_subtype_add_sum_subtype
                (fun p : ι → κ => Function.Injective p)
                (fun p => ∏ i, f (p i))
    _ = _ := by
      classical
      rw [← Fintype.piFinset_univ]
      rw [Finset.sum_prod_piFinset]
      simp [Finset.prod_const]

/-- Uniform finite majorant for all ordered injective selections from a
rectangular Taylor support.  This is the summation estimate that can absorb
the inverse-factorial product left by the Taylor coefficient bound. -/
theorem sum_injective_rectangularFactorialTaylorMass_le_exp_add_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ℝ) (N : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (∑ p : {p : ι → Fin N × Fin N // Function.Injective p}, ∏ i,
      (u ^ (p.1 i).1.1 / (Nat.factorial (p.1 i).1.1 : ℝ)) *
        (v ^ (p.1 i).2.1 / (Nat.factorial (p.1 i).2.1 : ℝ))) ≤
      (Real.exp (u + v)) ^ (Fintype.card ι) := by
  let f : Fin N × Fin N → ℝ := fun q =>
    (u ^ q.1.1 / (Nat.factorial q.1.1 : ℝ)) *
      (v ^ q.2.1 / (Nat.factorial q.2.1 : ℝ))
  have hf_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    exact mul_nonneg (div_nonneg (pow_nonneg hu _) (by positivity))
      (div_nonneg (pow_nonneg hv _) (by positivity))
  have hmass_nonneg : 0 ≤ rectangularFactorialTaylorMass u v N := by
    unfold rectangularFactorialTaylorMass
    apply Finset.sum_nonneg
    intro q _
    exact hf_nonneg q
  change (∑ p : {p : ι → Fin N × Fin N // Function.Injective p},
    ∏ i, f (p.1 i)) ≤ _
  calc
    (∑ p : {p : ι → Fin N × Fin N // Function.Injective p},
      ∏ i, f (p.1 i)) ≤
        (∑ q : Fin N × Fin N, f q) ^ (Fintype.card ι) :=
          sum_injective_prod_le_sum_pow f hf_nonneg
    _ = (rectangularFactorialTaylorMass u v N) ^ (Fintype.card ι) := by
      rfl
    _ ≤ (Real.exp (u + v)) ^ (Fintype.card ι) :=
      pow_le_pow_left₀ hmass_nonneg
        (rectangularFactorialTaylorMass_le_exp_add u v N hu hv) _

end PellPaper
