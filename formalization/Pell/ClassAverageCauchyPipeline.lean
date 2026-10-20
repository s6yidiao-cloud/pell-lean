import Pell.CauchyExceptional
import Pell.ClassAverageFinalReduction

/-!
# The finite class-average reduction from exceptional cardinalities

This module combines the ambient second moment with the exceptional-cardinality
estimate by Cauchy--Schwarz, and then applies the proved cutoff and integral
reduction.  Consequently the final bound needs no separate hypothesis on the
weighted exceptional sum.

The arithmetic inputs remain explicit: a pointwise class-number bound, a first
moment, a second moment, and an exponential bound for the number of indices
whose regulator parameter is small.  This conditional finite theorem does not
assert that those arithmetic inputs have been proved for quadratic fields.
-/

namespace PellPaper

open Set
open scoped BigOperators

noncomputable section

/-- The finite class-average estimate obtained from an exceptional-cardinality
bound and an ambient second moment.  Cauchy--Schwarz halves the exponential
rate, which is written as `2 * a` in the cardinality hypothesis. -/
theorem finite_sum_class_bound_of_exponential_cardinality
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (B₀ Ccard Cmoment r₀ a c X : ℝ)
    (hB₀ : 0 ≤ B₀) (hCcard : 0 ≤ Ccard) (hCmoment : 0 ≤ Cmoment)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (hc : 0 < c) (ha : 0 < a)
    (hX : Real.exp (Real.exp 1) ≤ X)
    (hT : r₀ ≤ classAverageCutoff c X)
    (hpoint : ∀ i ∈ s,
      h i ≤ (Real.sqrt X / Real.log X) * (L i / r i))
    (htotal : (∑ i ∈ s, L i) ≤ B₀ * X)
    (hmoment : (∑ i ∈ s, L i ^ 2) ≤ Cmoment * X)
    (hcard : ∀ θ ∈ Icc r₀ (classAverageCutoff c X),
      ((s.filter (fun i ↦ r i < θ)).card : ℝ) ≤
        Ccard * X * Real.exp (-2 * a * Real.log X / (θ + 1) ^ 2)) :
    (∑ i ∈ s, h i) ≤
      (B₀ / c + Real.sqrt (Ccard * Cmoment) *
        (((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt a)) * classAverageScale X := by
  have hXnonneg : 0 ≤ X := (Real.exp_pos _).le.trans hX
  apply finite_sum_class_bound_at_classAverageCutoff s h L r B₀
    (Real.sqrt (Ccard * Cmoment)) r₀ a c X hB₀ (Real.sqrt_nonneg _)
    hL hr hr₀ hc ha hX hT hpoint htotal
  intro θ hθ
  have hcard' : ((s.filter (fun i ↦ r i < θ)).card : ℝ) ≤
      Ccard * X * Real.exp (-2 * a * (Real.log X / (θ + 1) ^ 2)) := by
    simpa only [mul_div_assoc] using hcard θ hθ
  have hweighted := exceptional_sum_le_exp_of_card_le s
    (s.filter (fun i ↦ r i < θ)) L X Ccard Cmoment a
    (Real.log X / (θ + 1) ^ 2) (Finset.filter_subset _ _) hXnonneg
    hCcard hCmoment hcard' hmoment
  simpa only [mul_div_assoc] using hweighted

/-- The same estimate with the cardinality decay rate stated directly as `a`.
The corresponding weighted rate is `a / 2`, reflected in the explicit
constant of the final class-average bound. -/
theorem finite_sum_class_bound_of_exponential_cardinality_rate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (B₀ Ccard Cmoment r₀ a c X : ℝ)
    (hB₀ : 0 ≤ B₀) (hCcard : 0 ≤ Ccard) (hCmoment : 0 ≤ Cmoment)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (hc : 0 < c) (ha : 0 < a)
    (hX : Real.exp (Real.exp 1) ≤ X)
    (hT : r₀ ≤ classAverageCutoff c X)
    (hpoint : ∀ i ∈ s,
      h i ≤ (Real.sqrt X / Real.log X) * (L i / r i))
    (htotal : (∑ i ∈ s, L i) ≤ B₀ * X)
    (hmoment : (∑ i ∈ s, L i ^ 2) ≤ Cmoment * X)
    (hcard : ∀ θ ∈ Icc r₀ (classAverageCutoff c X),
      ((s.filter (fun i ↦ r i < θ)).card : ℝ) ≤
        Ccard * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) :
    (∑ i ∈ s, h i) ≤
      (B₀ / c + Real.sqrt (Ccard * Cmoment) *
        (((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt (a / 2))) * classAverageScale X := by
  apply finite_sum_class_bound_of_exponential_cardinality s h L r
    B₀ Ccard Cmoment r₀ (a / 2) c X hB₀ hCcard hCmoment
    hL hr hr₀ hc (half_pos ha) hX hT hpoint htotal hmoment
  intro θ hθ
  convert hcard θ hθ using 1
  congr 2
  ring

end

end PellPaper
