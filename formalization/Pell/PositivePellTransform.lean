import Pell.PellEpsilonMultiplicative

/-!
# Positive cyclic transport for supplied Pell transformations

These lemmas concern a supplied literal `Pell.Solution₁ (u * v)` acting on
integer pairs by `(e,d) ↦ (q.x*e + u*q.y*d, v*q.y*e + q.x*d)`.
If the corresponding two real quadratic values are positive, Mathlib's
signed-power classification has only its positive branch.

No fixed-norm equation, congruence hypothesis, orbit count or height estimate
is proved or needed here. Existence of a transport remains a separate input.
-/

namespace PellPaper

/-- A norm-one Pell solution with positive real value is an integral power of
any supplied fundamental solution. No coordinate positivity of `q` is needed. -/
theorem exists_eq_zpow_of_epsilon_pos {D : ℤ}
    {a₀ : Pell.Solution₁ D} (ha₀ : Pell.IsFundamental a₀)
    (q : Pell.Solution₁ D) (hq : 0 < epsilon q) :
    ∃ n : ℤ, q = a₀ ^ n := by
  obtain ⟨n, hn | hn⟩ := ha₀.eq_zpow_or_neg_zpow q
  · exact ⟨n, hn⟩
  · have hp := epsilon_zpow_pos_of_isFundamental ha₀ n
    rw [hn, epsilon_neg] at hq
    linarith

/-- The literal integer Pell action multiplies the real quadratic value by
`epsilon q`, for every nonnegative product radicand. Individual parameters
and coordinates may have either sign, and may be zero. -/
theorem pell_transform_real_value
    (u v d e d' e' : ℤ) (huv : 0 ≤ u * v)
    (q : Pell.Solution₁ (u * v))
    (he : e' = q.x * e + u * q.y * d)
    (hd : d' = v * q.y * e + q.x * d) :
    (v : ℝ) * e' + (d' : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) =
      epsilon q * ((v : ℝ) * e + (d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) := by
  have huvR : (0 : ℝ) ≤ ((u * v : ℤ) : ℝ) := by exact_mod_cast huv
  have hs := Real.sq_sqrt huvR
  rw [he, hd, epsilon]
  push_cast at hs ⊢
  linear_combination -(q.y : ℝ) * (d : ℝ) * hs

/-- If a supplied Pell transform carries a pair with positive real quadratic
value to another such pair, it is a power of a supplied fundamental solution.
The norm level may have either sign: no norm equation is used in this lemma. -/
theorem exists_eq_zpow_of_positive_pell_transform
    (u v d e d' e' : ℤ)
    {a₀ : Pell.Solution₁ (u * v)} (ha₀ : Pell.IsFundamental a₀)
    (q : Pell.Solution₁ (u * v))
    (he : e' = q.x * e + u * q.y * d)
    (hd : d' = v * q.y * e + q.x * d)
    (hα : 0 < (v : ℝ) * e + (d : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ))
    (hα' : 0 < (v : ℝ) * e' + (d' : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) :
    ∃ n : ℤ, q = a₀ ^ n := by
  apply exists_eq_zpow_of_epsilon_pos ha₀ q
  rw [pell_transform_real_value u v d e d' e' ha₀.d_pos.le q he hd] at hα'
  exact (mul_pos_iff_of_pos_right hα).mp hα'

end PellPaper
