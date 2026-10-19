import Mathlib.Tactic

/-!
# Shared elementary full-cell square-sieve envelope

The elementary projective character-sum estimate gives a degree-free
`O(N^3)` Fourier error.  This module records the common envelope used by both
the balanced and large-analytic branches.
-/

namespace PellPaper

noncomputable section

/-- The full-cell square-sieve envelope obtained from the unconditional local
Fourier constant `3 * sqrt N`.  The degree argument is deliberately retained
for compatibility with the existing degree-indexed aggregation APIs, although
the value is independent of it. -/
def fullCellElementarySieveEnvelope
    (N _d : ℕ) (U V M mu : ℝ) : ℝ :=
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  (4608 / Real.log 2) * (U * V / M) *
      Real.log (N : ℝ) / (N : ℝ) +
    576 * (N : ℝ) ^ 3 * Llog ^ 2 +
    864 * (N : ℝ) * Llog / mu

/-- Positivity of the elementary envelope. -/
theorem fullCellElementarySieveEnvelope_nonnegative
    (N d : ℕ) (U V M mu : ℝ) (hN : 4 ≤ N)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hmu : 0 < mu) :
    0 ≤ fullCellElementarySieveEnvelope N d U V M mu := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    nlinarith [sq_nonneg (N : ℝ)]
  have hLlog : 0 ≤ 1 + Real.log (16 * (N : ℝ) ^ 2) := by
    linarith [Real.log_nonneg harg]
  rw [fullCellElementarySieveEnvelope]
  positivity

end

end PellPaper
