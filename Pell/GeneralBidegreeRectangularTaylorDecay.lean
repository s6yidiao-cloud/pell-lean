import Pell.GeneralBidegreeFiniteTaylorCauchyBinetDecay
import Pell.GeneralBidegreeTaylorTailMajorant
import Pell.GeneralBidegreeTwoRegimeWeightedFiltration
import Pell.ShearedExponentialEvaluationMatrixAlignment

/-!
# Uniform finite decay for rectangular sheared Taylor truncations

This module combines the finite weighted Cauchy--Binet estimate with the
factorial Taylor mass bound for a literal rectangular support.  Given a
lower bound for every nonzero coefficient minor's total logarithmic weight,
it produces a Taylor-determinant bound uniform in the truncation order.

The remaining inputs needed for `L:sheared` are the sharp lower bound for the
selected weights and the source-specific local-coordinate / minor bounds.
-/

namespace PellPaper

open scoped BigOperators

/-- A nonzero real selected coefficient minor forces the corresponding
rational monomial-evaluation minor to be nonzero.  This is the exact bridge
from the real Cauchy--Binet coefficient factor to the rational rank
filtration. -/
theorem generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_real_submatrix_det_ne_zero
    {κ : Type*} [Fintype κ]
    (A B : ℕ) (s : κ → generalBidegreeCoefficientMonomialIndex)
    (p : generalBidegreeGrid A B → κ)
    (hreal :
      ((generalBidegreeRectangularCoefficientMatrixReal A B s).submatrix id p).det ≠ 0) :
    (generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p)).det ≠ 0 := by
  intro hzero
  apply hreal
  change (((generalBidegreeRectangularCoefficientMatrix A B s).map
    (algebraMap ℚ ℝ)).submatrix id p).det = 0
  have hmatrix :
      (generalBidegreeRectangularCoefficientMatrix A B s).submatrix id p =
        generalBidegreeSelectedCoefficientEvaluationMatrix A B (s ∘ p) := by
    rfl
  change (((algebraMap ℚ ℝ).mapMatrix
    ((generalBidegreeRectangularCoefficientMatrix A B s).submatrix id p)).det) = 0
  rw [← (algebraMap ℚ ℝ).map_det, hmatrix, hzero, map_zero]

/-- The two literal coordinates of a point in `Γ_(A,B)` have their evident
uniform absolute bounds. -/
theorem generalBidegreeGrid_coordinate_abs_bounds
    (A B : ℕ) (r : generalBidegreeGrid A B) :
    |(r.1.1 : ℝ)| ≤ ((A + 2 * B : ℕ) : ℝ) ∧ |(r.1.2 : ℝ)| ≤ (B : ℝ) := by
  rcases mem_generalBidegreeGrid_iff.mp r.2 with ⟨a, b, ha, hb, hfst, hsnd⟩
  have hr : r.1 = (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) :=
    Prod.ext hfst hsnd
  rw [hr]
  constructor
  · change |((a + 2 * b : ℕ) : ℝ)| ≤ ((A + 2 * B : ℕ) : ℝ)
    rw [abs_of_nonneg]
    · exact_mod_cast Nat.add_le_add ha (Nat.mul_le_mul_left 2 hb)
    · positivity
  · change |(b : ℝ)| ≤ (B : ℝ)
    rw [abs_of_nonneg]
    · exact_mod_cast hb
    · positivity

/-- A rectangular coefficient-evaluation entry is bounded by the matching
two powers of uniform coordinate bounds. -/
theorem abs_generalBidegreeRectangularCoefficientMatrixReal_rectangularTaylorSupport_le_pows
    (A B N : ℕ) (u v : ℝ) (hu : 0 ≤ u)
    (hcoords : ∀ r : generalBidegreeGrid A B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (r : generalBidegreeGrid A B) (q : Fin N × Fin N) :
    |generalBidegreeRectangularCoefficientMatrixReal A B
      (generalBidegreeRectangularTaylorSupport N) r q| ≤
      u ^ q.1.1 * v ^ q.2.1 := by
  rw [generalBidegreeRectangularCoefficientMatrixReal_rectangularTaylorSupport_apply,
    abs_mul, abs_pow, abs_pow]
  exact mul_le_mul
    (pow_le_pow_left₀ (abs_nonneg _) (hcoords r).1 _)
    (pow_le_pow_left₀ (abs_nonneg _) (hcoords r).2 _)
    (pow_nonneg (abs_nonneg _) _) (pow_nonneg hu _)

/-- The residual Cauchy--Binet mass for a rectangular Taylor support is the
literal factorial Taylor mass. -/
theorem sum_rectangularCoefficientScale_mul_invFactorials_eq_rectangularFactorialTaylorMass
    (u v : ℝ) (N : ℕ) :
    (∑ q : Fin N × Fin N,
      (u ^ q.1.1 * v ^ q.2.1) *
        ((Nat.factorial q.1.1 : ℝ)⁻¹ * (Nat.factorial q.2.1 : ℝ)⁻¹)) =
      rectangularFactorialTaylorMass u v N := by
  unfold rectangularFactorialTaylorMass
  apply Finset.sum_congr rfl
  intro q _
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- A finite rectangular Taylor determinant has uniform exponential decay
once every nonzero rectangular coefficient minor has total logarithmic
weight at least `W`.  The factor independent of the truncation is explicit.
-/
theorem abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_factorial_mul_exp_neg_minWeight_mul_exp_tail
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (u v ellM ellX W : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid A B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hweight : ∀ p :
      {p : generalBidegreeGrid A B → Fin N × Fin N // Function.Injective p},
      ((generalBidegreeRectangularCoefficientMatrixReal A B
        (generalBidegreeRectangularTaylorSupport N)).submatrix id p.1).det ≠ 0 →
        W ≤ ∑ i, generalBidegreeRealWeight ellM ellX
          (generalBidegreeRectangularTaylorSupport N (p.1 i)))
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeRectangularTaylorEvaluationMatrix A B α β N).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-W) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid A B) := by
  have hfinite :=
    abs_det_generalBidegreeFiniteTaylorEvaluationMatrix_le_factorial_mul_exp_neg_minWeight_mul_sum_invFactorials_pow
      A B α β (generalBidegreeRectangularTaylorSupport N)
      (fun q => u ^ q.1.1 * v ^ q.2.1) ellM ellX W
      (fun q => mul_nonneg (pow_nonneg hu _) (pow_nonneg hv _))
      (fun r q =>
        abs_generalBidegreeRectangularCoefficientMatrixReal_rectangularTaylorSupport_le_pows
          A B N u v hu hcoords r q)
      hweight hα hβ
  rw [generalBidegreeFiniteTaylorEvaluationMatrix_rectangularTaylorSupport] at hfinite
  simp only [generalBidegreeRectangularTaylorSupport_zero,
    generalBidegreeRectangularTaylorSupport_one] at hfinite
  calc
    |(generalBidegreeRectangularTaylorEvaluationMatrix A B α β N).det| ≤
        (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
          Real.exp (-W) *
          (∑ q : Fin N × Fin N,
            (u ^ q.1.1 * v ^ q.2.1) *
              ((Nat.factorial q.1.1 : ℝ)⁻¹ *
                (Nat.factorial q.2.1 : ℝ)⁻¹)) ^
              Fintype.card (generalBidegreeGrid A B) := hfinite
    _ = (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
          Real.exp (-W) *
          (rectangularFactorialTaylorMass u v N) ^
              Fintype.card (generalBidegreeGrid A B) := by
        rw [sum_rectangularCoefficientScale_mul_invFactorials_eq_rectangularFactorialTaylorMass]
    _ ≤ (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
          Real.exp (-W) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid A B) := by
        apply mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (Finset.sum_nonneg fun q _ =>
              mul_nonneg (div_nonneg (pow_nonneg hu _) (by positivity))
                (div_nonneg (pow_nonneg hv _) (by positivity)))
            (rectangularFactorialTaylorMass_le_exp_add u v N hu hv) _)
        exact mul_nonneg (by positivity) (Real.exp_pos _).le

/-- The two-regime rank filtration supplies the required total-weight lower
bound for every nonzero *real* rectangular coefficient minor, after the
preceding real-to-rational minor bridge. -/
theorem scaledTwoRegimeDeficits_le_totalWeight_of_real_rectangularCoefficientMinor_ne_zero
    (A B N : ℕ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hmesh : 0 < mesh) (Q : ℕ)
    (p : {p : generalBidegreeGrid A B → Fin N × Fin N // Function.Injective p})
    (hreal :
      ((generalBidegreeRectangularCoefficientMatrixReal A B
        (generalBidegreeRectangularTaylorSupport N)).submatrix id p.1).det ≠ 0) :
    (∑ n ∈ Finset.range Q,
      ((Fintype.card (generalBidegreeGrid A B) -
        generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh ≤
      ∑ i, generalBidegreeRealWeight ellM ellX
        (generalBidegreeRectangularTaylorSupport N (p.1 i)) := by
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledTwoRegimeDeficits_of_det_ne_zero
    A B (generalBidegreeRectangularTaylorSupport N ∘ p.1)
    (fun i => generalBidegreeRealWeight ellM ellX
      (generalBidegreeRectangularTaylorSupport N (p.1 i)))
    ellM ellX mesh hellM_pos hell
  · intro i
    rfl
  · exact
      generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_real_submatrix_det_ne_zero
        A B (generalBidegreeRectangularTaylorSupport N) p.1 hreal
  · exact hmesh

/-- **Finite two-regime determinant decay.**  The literal rectangular Taylor
truncation has the two-regime greedy exponent, with a Taylor-tail constant
uniform in the truncation order.  This is a finite quantitative counterpart
of the determinant estimate in `L:sheared`; evaluating its deficit sum and
transporting it to the source local coordinates remain separate. -/
theorem abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_twoRegime_exp_tail
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (u v ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid A B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeRectangularTaylorEvaluationMatrix A B α β N).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-(
          (∑ n ∈ Finset.range Q,
            ((Fintype.card (generalBidegreeGrid A B) -
              generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
                (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh)) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid A B) := by
  apply abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_factorial_mul_exp_neg_minWeight_mul_exp_tail
    A B N α β u v ellM ellX
    ((∑ n ∈ Finset.range Q,
      ((Fintype.card (generalBidegreeGrid A B) -
        generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
          (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh)
    hu hv hcoords ?_ hα hβ
  intro p hp
  exact scaledTwoRegimeDeficits_le_totalWeight_of_real_rectangularCoefficientMinor_ne_zero
    A B N ellM ellX mesh hellM_pos hell hmesh Q p hp

/-- The uniform finite estimate survives the rectangular Taylor limit and
therefore bounds the literal sheared exponential evaluation determinant.
This is the analytic Cauchy--Binet handoff: no nonvanishing assumption is
used, and the right-hand side remains the same for every Taylor cutoff. -/
theorem abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoRegime_exp_tail
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (u v ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid A B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeExponentialEvaluationMatrix A B α β).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-(
          (∑ n ∈ Finset.range Q,
            ((Fintype.card (generalBidegreeGrid A B) -
              generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
                (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh)) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid A B) := by
  apply le_of_tendsto'
    (tendsto_det_generalBidegreeRectangularTaylorEvaluationMatrix A B α β).abs
  intro N
  exact abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_twoRegime_exp_tail
    A B N α β u v ellM ellX mesh hellM_pos hell hmesh Q hu hv hcoords hα hβ

/-- The preceding exponential determinant estimate with the coordinate
bounds intrinsic to the literal sheared grid substituted explicitly. -/
theorem abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoRegime_exp_tail_gridBounds
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeExponentialEvaluationMatrix A B α β).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-(
          (∑ n ∈ Finset.range Q,
            ((Fintype.card (generalBidegreeGrid A B) -
              generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
                (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh)) *
          (Real.exp (((A + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid A B) := by
  apply abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoRegime_exp_tail
    A B α β ((A + 2 * B : ℕ) : ℝ) (B : ℝ) ellM ellX mesh
    hellM_pos hell hmesh Q (by positivity) (by positivity)
    (generalBidegreeGrid_coordinate_abs_bounds A B) hα hβ

/-- Source-side version of the literal exponential determinant estimate.
The arbitrary source rows and the natural bidegree columns are reindexed to
the Taylor-limit grid; all quantitative hypotheses are stated directly for
the two reindexed local logarithms. -/
theorem abs_det_reindex_shearedExponentialEvaluationMatrix_le_twoRegime_exp_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (S T : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ r,
      |generalBidegreeReindexedLogS A B eRows S r| ≤ Real.exp (-ellM))
    (hβ : ∀ r,
      |generalBidegreeReindexedShearedLogT A B eRows S T r| ≤ Real.exp (-ellX)) :
    |(Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
      (shearedExponentialEvaluationMatrix A B S T)).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-(
          (∑ n ∈ Finset.range Q,
            ((Fintype.card (generalBidegreeGrid A B) -
              generalBidegreePositiveRealWeightedTwoRegimeRankCap A ellM ellX
                (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) * mesh)) *
          (Real.exp (((A + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid A B) := by
  calc
    |(Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
        (shearedExponentialEvaluationMatrix A B S T)).det| =
        |(generalBidegreeShearedExponentialEvaluationMatrix A B
        (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T)).det| := by
          rw [reindex_shearedExponentialEvaluationMatrix_eq_generalBidegreeSheared]
    _ = |(generalBidegreeExponentialEvaluationMatrix A B
        (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T)).det| := by
          rw [generalBidegreeExponentialEvaluationMatrix_eq_sheared]
    _ ≤ _ :=
      abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoRegime_exp_tail_gridBounds
        A B (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T)
        ellM ellX mesh hellM_pos hell hmesh Q hα hβ

end PellPaper
