import Pell.ClassAverage

/-!
# Finite cutoff reduction for class-number averages

This module isolates the elementary finite-sum step used near the end of the proof
of the class-number average in `main.tex`.  It does not assert the analytic class-number
estimate.  Instead, it turns pointwise bounds of the shape
`h i ≤ A * L i / r i` into a bound involving the numerator sums on the two sides of a
cutoff for `r`.

In the intended arithmetic application, `s` is the set of positive fundamental
discriminants in the large-discriminant range, `L i` is `L(1, χ_D)`, `r i` is
`log η_{K_D} / log D`, and `h i` is an ordinary or form class number.  A future
instantiation must provide the following inputs from the upstream argument:

* nonnegativity of the real quadratic `L`-values;
* a uniform positive lower bound `r₀ ≤ r i`, obtained from the elementary unit bound;
* the pointwise inequality `h i ≤ A * (L i / r i)`, obtained from the class-number
  formula (and the comparison between ordinary and form class numbers when needed);
* bounds for the two filtered numerator sums.  In the manuscript, the lower-cutoff
  bound comes from the uniform exceptional-set estimate together with the second
  moment and Cauchy's inequality, while the upper-cutoff bound follows from the
  second moment and a count of fundamental discriminants.

The results below prove only the finite order manipulations once those estimates have
been supplied.
-/

namespace PellPaper

noncomputable section

/-- Reduce a sum satisfying pointwise class-number-formula bounds to two weighted
numerator sums, split according to whether the ratio is at most the cutoff `T`.

The assumptions `0 < r₀` and `r₀ ≤ r i` in particular ensure that every denominator
is positive.  Nonnegativity of `A` is the sign condition needed to preserve the
finite-sum estimate when the bound from `finite_sum_div_split` is scaled. -/
theorem finite_sum_class_bound_cutoff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (A r₀ T : ℝ)
    (hA : 0 ≤ A)
    (hL : ∀ i ∈ s, 0 ≤ L i)
    (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀)
    (hT : r₀ ≤ T)
    (hpoint : ∀ i ∈ s, h i ≤ A * (L i / r i)) :
    (∑ i ∈ s, h i) ≤
      A * ((∑ i ∈ s.filter fun i ↦ r i ≤ T, L i) / r₀ +
        (∑ i ∈ s.filter fun i ↦ T < r i, L i) / T) := by
  calc
    (∑ i ∈ s, h i) ≤ ∑ i ∈ s, A * (L i / r i) := by
      exact Finset.sum_le_sum fun i hi ↦ hpoint i hi
    _ = A * ∑ i ∈ s, L i / r i := by
      simp only [Finset.mul_sum]
    _ ≤ A * ((∑ i ∈ s.filter fun i ↦ r i ≤ T, L i) / r₀ +
        (∑ i ∈ s.filter fun i ↦ T < r i, L i) / T) := by
      exact mul_le_mul_of_nonneg_left
        (finite_sum_div_split s L r r₀ T hL hr hr₀ hT) hA

/-- A convenient interface for later analytic work: raw upper bounds for the two
cutoff numerator sums can be substituted directly into the class-number sum bound.

For the application in `main.tex`, `Bₗₒ` must be proved using the exceptional-set
estimate, the `L(1, χ_D)` second moment, and Cauchy's inequality.  The bound `Bₕᵢ`
must be supplied from the corresponding unrestricted first-moment estimate (itself
deduced there from the second moment).  The theorem makes no claim that these
analytic estimates or the arithmetic interpretation of `h`, `L`, and `r` have
already been formalized. -/
theorem finite_sum_class_bound_of_cutoff_numerators {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (A r₀ T Bₗₒ Bₕᵢ : ℝ)
    (hA : 0 ≤ A)
    (hL : ∀ i ∈ s, 0 ≤ L i)
    (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀)
    (hT : r₀ ≤ T)
    (hpoint : ∀ i ∈ s, h i ≤ A * (L i / r i))
    (hlow : (∑ i ∈ s.filter fun i ↦ r i ≤ T, L i) ≤ Bₗₒ)
    (hhigh : (∑ i ∈ s.filter fun i ↦ T < r i, L i) ≤ Bₕᵢ) :
    (∑ i ∈ s, h i) ≤ A * (Bₗₒ / r₀ + Bₕᵢ / T) := by
  have hTpos : 0 < T := hr₀.trans_le hT
  calc
    (∑ i ∈ s, h i) ≤
        A * ((∑ i ∈ s.filter fun i ↦ r i ≤ T, L i) / r₀ +
          (∑ i ∈ s.filter fun i ↦ T < r i, L i) / T) :=
      finite_sum_class_bound_cutoff s h L r A r₀ T hA hL hr hr₀ hT hpoint
    _ ≤ A * (Bₗₒ / r₀ + Bₕᵢ / T) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add
        (div_le_div_of_nonneg_right hlow hr₀.le)
        (div_le_div_of_nonneg_right hhigh hTpos.le)

end

end PellPaper
