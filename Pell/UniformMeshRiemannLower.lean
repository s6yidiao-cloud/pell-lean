import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A finite right-Riemann lower bound with an explicit endpoint error

The determinant filtration is a sum over a uniform mesh of an antitone
rank-deficit envelope.  This elementary lemma compares that finite right sum
to its interval integral without taking a limit: the only loss is the first
mesh interval.  It is intended to make the `O(B²)` mesh error in the sheared
cubic calculation explicit.
-/

namespace PellPaper

open scoped BigOperators Interval
open Set MeasureTheory

noncomputable section

/-- The unscaled left and right samples of a function on a uniform mesh
telescopically differ only at the two endpoints. -/
theorem sum_uniformMesh_left_eq_right_add_endpoint
    (f : ℝ → ℝ) (h : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f ((i : ℝ) * h)) =
      (∑ i ∈ Finset.range N, f (((i + 1 : ℕ) : ℝ) * h)) +
        f 0 - f ((N : ℝ) * h) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      ring

/-- For an antitone function, its finite right Riemann sum at a positive
uniform mesh is at least the interval integral minus the exact endpoint
loss from the first mesh cell. -/
theorem uniformMesh_rightRiemannSum_ge_integral_sub_endpoint
    (f : ℝ → ℝ) (h : ℝ) (N : ℕ) (hh : 0 < h)
    (hanti : AntitoneOn f (Icc 0 ((N : ℝ) * h))) :
    (∫ x in 0..(N : ℝ) * h, f x) -
        h * (f 0 - f ((N : ℝ) * h)) ≤
      h * ∑ i ∈ Finset.range N, f (((i + 1 : ℕ) : ℝ) * h) := by
  let g : ℝ → ℝ := fun t => f (t * h)
  have hganti : AntitoneOn g (Icc 0 (N : ℝ)) := by
    intro s hs t ht hst
    apply hanti
    · constructor
      · exact mul_nonneg hs.1 hh.le
      · simpa [g, mul_assoc] using
          (mul_le_mul_of_nonneg_right hs.2 hh.le)
    · constructor
      · exact mul_nonneg ht.1 hh.le
      · simpa [g, mul_assoc] using
          (mul_le_mul_of_nonneg_right ht.2 hh.le)
    · exact mul_le_mul_of_nonneg_right hst hh.le
  have hintegral :
      (∫ t in 0..(N : ℝ), g t) ≤
        ∑ i ∈ Finset.range N, g ((i : ℝ)) := by
    have hganti' : AntitoneOn g (Icc 0 (0 + (N : ℝ))) := by
      simpa using hganti
    simpa using (hganti'.integral_le_sum (x₀ := 0) (a := N))
  have hscaled :
      h * (∫ t in 0..(N : ℝ), g t) ≤
        h * ∑ i ∈ Finset.range N, g ((i : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hintegral hh.le
  have hchange :
      h * (∫ t in 0..(N : ℝ), g t) =
        ∫ x in 0..(N : ℝ) * h, f x := by
    change h * (∫ t in 0..(N : ℝ), f (t * h)) = _
    simp [intervalIntegral.mul_integral_comp_mul_right]
  have htele := sum_uniformMesh_left_eq_right_add_endpoint f h N
  change (∫ x in 0..(N : ℝ) * h, f x) -
      h * (f 0 - f ((N : ℝ) * h)) ≤ _
  rw [← hchange] 
  calc
    h * (∫ t in 0..(N : ℝ), g t) -
        h * (f 0 - f ((N : ℝ) * h)) ≤
        h * ∑ i ∈ Finset.range N, g ((i : ℝ)) -
          h * (f 0 - f ((N : ℝ) * h)) := by
            linarith
    _ = h * ∑ i ∈ Finset.range N, f (((i + 1 : ℕ) : ℝ) * h) := by
          change h * (∑ i ∈ Finset.range N, f ((i : ℝ) * h)) -
              h * (f 0 - f ((N : ℝ) * h)) = _
          rw [htele]
          ring

end

end PellPaper
