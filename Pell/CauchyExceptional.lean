import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Cauchy--Schwarz for weighted exceptional sets

The proof of the class-number average in `main.tex` uses a second-moment bound
on all discriminants and a cardinality bound on an exceptional subset.  This
module proves that finite analytic step, including the factor of two lost in
the exponential rate when passing from a count to a weighted sum.

The weights may be arbitrary real numbers: the upper bounds proved here do
not require their nonnegativity.  The second-moment and exceptional-cardinality
estimates are hypotheses, whose arithmetic proofs are separate obligations.
-/

namespace PellPaper

noncomputable section

/-- The second moment over a subset is bounded by that over the ambient set. -/
theorem second_moment_mono {ι : Type*} (s t : Finset ι) (L : ι → ℝ)
    (hts : t ⊆ s) :
    (∑ i ∈ t, L i ^ 2) ≤ ∑ i ∈ s, L i ^ 2 := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hts (fun i _ _ ↦ sq_nonneg (L i))

/-- Cauchy--Schwarz with an ambient second-moment bound. -/
theorem exceptional_sum_sq_le {ι : Type*} (s t : Finset ι) (L : ι → ℝ)
    (M : ℝ) (hts : t ⊆ s) (hmoment : (∑ i ∈ s, L i ^ 2) ≤ M) :
    (∑ i ∈ t, L i) ^ 2 ≤ (t.card : ℝ) * M := by
  have hcauchy : (∑ i ∈ t, L i) ^ 2 ≤
      (t.card : ℝ) * ∑ i ∈ t, L i ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq t (fun _ ↦ (1 : ℝ)) L
  exact hcauchy.trans <| mul_le_mul_of_nonneg_left
    ((second_moment_mono s t L hts).trans hmoment) (Nat.cast_nonneg _)

/-- A square-root bound requiring no choice of a cardinality majorant. -/
theorem exceptional_sum_le_sqrt {ι : Type*} (s t : Finset ι) (L : ι → ℝ)
    (M : ℝ) (hts : t ⊆ s) (hmoment : (∑ i ∈ s, L i ^ 2) ≤ M) :
    (∑ i ∈ t, L i) ≤ Real.sqrt ((t.card : ℝ) * M) := by
  exact Real.le_sqrt_of_sq_le (exceptional_sum_sq_le s t L M hts hmoment)

/-- Replace the cardinality by any real upper bound.  Nonnegativity of the
second-moment majorant follows from its defining inequality. -/
theorem exceptional_sum_sq_le_of_card_le {ι : Type*}
    (s t : Finset ι) (L : ι → ℝ) (N M : ℝ) (hts : t ⊆ s)
    (hcard : (t.card : ℝ) ≤ N) (hmoment : (∑ i ∈ s, L i ^ 2) ≤ M) :
    (∑ i ∈ t, L i) ^ 2 ≤ N * M := by
  have hM : 0 ≤ M :=
    (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (L i))).trans hmoment
  exact (exceptional_sum_sq_le s t L M hts hmoment).trans
    (mul_le_mul_of_nonneg_right hcard hM)

/-- The square-root form with both cardinality and moment majorants. -/
theorem exceptional_sum_le_sqrt_of_card_le {ι : Type*}
    (s t : Finset ι) (L : ι → ℝ) (N M : ℝ) (hts : t ⊆ s)
    (hcard : (t.card : ℝ) ≤ N) (hmoment : (∑ i ∈ s, L i ^ 2) ≤ M) :
    (∑ i ∈ t, L i) ≤ Real.sqrt (N * M) := by
  exact Real.le_sqrt_of_sq_le
    (exceptional_sum_sq_le_of_card_le s t L N M hts hcard hmoment)

/-- A linear bound is available as soon as the product of the cardinality and
second-moment majorants is bounded by the square of a nonnegative quantity. -/
theorem exceptional_sum_le_of_product_le_sq {ι : Type*}
    (s t : Finset ι) (L : ι → ℝ) (N M B : ℝ) (hts : t ⊆ s)
    (hcard : (t.card : ℝ) ≤ N) (hmoment : (∑ i ∈ s, L i ^ 2) ≤ M)
    (hB : 0 ≤ B) (hproduct : N * M ≤ B ^ 2) :
    (∑ i ∈ t, L i) ≤ B := by
  exact le_of_sq_le_sq
    ((exceptional_sum_sq_le_of_card_le s t L N M hts hcard hmoment).trans hproduct)
    hB

/-- An exponentially small exceptional set and a linear second moment give
an exponentially small first moment, with the exponential rate halved.

Taking `u = log X / (θ + 1)^2` gives the weighted exceptional-set estimate in
the proof of the class-number average.  No sign condition on `a` or `u` is
needed for this implication; positivity is relevant to interpreting decay. -/
theorem exceptional_sum_le_exp_of_card_le {ι : Type*}
    (s t : Finset ι) (L : ι → ℝ) (X Ccard Cmoment a u : ℝ)
    (hts : t ⊆ s) (hX : 0 ≤ X) (hCcard : 0 ≤ Ccard) (hCmoment : 0 ≤ Cmoment)
    (hcard : (t.card : ℝ) ≤ Ccard * X * Real.exp (-2 * a * u))
    (hmoment : (∑ i ∈ s, L i ^ 2) ≤ Cmoment * X) :
    (∑ i ∈ t, L i) ≤
      Real.sqrt (Ccard * Cmoment) * X * Real.exp (-a * u) := by
  apply exceptional_sum_le_of_product_le_sq s t L
    (Ccard * X * Real.exp (-2 * a * u)) (Cmoment * X) _ hts hcard hmoment
  · positivity
  · have hexp : Real.exp (-2 * a * u) = Real.exp (-a * u) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hCcard hCmoment)]
    ring_nf
    exact le_rfl

/-- Normalized exponential weighted-count bound, in the form used in `main.tex`. -/
theorem exceptional_sum_div_le_exp_of_card_le {ι : Type*}
    (s t : Finset ι) (L : ι → ℝ) (X Ccard Cmoment a u : ℝ)
    (hts : t ⊆ s) (hX : 0 < X) (hCcard : 0 ≤ Ccard) (hCmoment : 0 ≤ Cmoment)
    (hcard : (t.card : ℝ) ≤ Ccard * X * Real.exp (-2 * a * u))
    (hmoment : (∑ i ∈ s, L i ^ 2) ≤ Cmoment * X) :
    (∑ i ∈ t, L i) / X ≤
      Real.sqrt (Ccard * Cmoment) * Real.exp (-a * u) := by
  apply (div_le_iff₀ hX).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    exceptional_sum_le_exp_of_card_le s t L X Ccard Cmoment a u
      hts hX.le hCcard hCmoment hcard hmoment

end

end PellPaper
