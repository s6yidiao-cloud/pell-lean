import Pell.ShiftedSquareBlock
import Pell.QuadraticOrderPellTraceNorm
import Mathlib.Tactic

/-!
# The first quadratic-integer package for shifted squares

For a shifted-square solution `d^2 w = n^2 + a`, the manuscript uses

`q₂ = 2` when `d` is even and `q₂ = 1` otherwise, `d₀ = d / q₂`, and
`ζ = (n + sqrt(-a)) / q₂`.

Mathlib's `QuadraticAlgebra` is constructed before its no-rational-root field
instance is installed, so literal division inside that algebra is needlessly
restrictive.  We therefore define `ζ` by its mathematically equivalent
coordinates `(n/q₂, 1/q₂)` in the basis `1, omega` of
`rationalQuadraticAlgebra (-a)`.  The exact trace and norm computations below
verify that this is the intended element.

This file contains only the elementary algebraic beginning of
`L:square-map-coordinates`.  It makes no ideal-factorization, Minkowski, or
uniform shifted-square counting assertion.
-/

namespace PellPaper

noncomputable section

/-- The parity normalization from `L:square-map-coordinates`. -/
def shiftedSquareQ₂ (d : ℕ) : ℕ :=
  if Even d then 2 else 1

/-- The source coordinate after removing the parity normalization. -/
def shiftedSquareD₀ (d : ℕ) : ℕ :=
  d / shiftedSquareQ₂ d

/-- The integral trace of the normalized quadratic element. -/
def shiftedSquareZetaTrace (d n : ℕ) : ℕ :=
  if Even d then n else 2 * n

/-- The element `(n + sqrt(-a))/q₂`, represented by its two rational
coordinates in `rationalQuadraticAlgebra (-a)`. -/
def shiftedSquareZeta (a : ℤ) (d n : ℕ) :
    rationalQuadraticAlgebra (-a) :=
  ⟨(n : ℚ) / (shiftedSquareQ₂ d : ℚ),
    1 / (shiftedSquareQ₂ d : ℚ)⟩

@[simp] theorem shiftedSquareQ₂_eq_two_of_even {d : ℕ} (hd : Even d) :
    shiftedSquareQ₂ d = 2 := by
  simp [shiftedSquareQ₂, hd]

@[simp] theorem shiftedSquareQ₂_eq_one_of_not_even {d : ℕ}
    (hd : ¬ Even d) : shiftedSquareQ₂ d = 1 := by
  simp [shiftedSquareQ₂, hd]

theorem shiftedSquareQ₂_pos (d : ℕ) : 0 < shiftedSquareQ₂ d := by
  by_cases hd : Even d <;> simp [shiftedSquareQ₂, hd]

/-- The parity factor and quotient reconstruct `d` exactly. -/
theorem shiftedSquareQ₂_mul_D₀ (d : ℕ) :
    shiftedSquareQ₂ d * shiftedSquareD₀ d = d := by
  by_cases hd : Even d
  · simp only [shiftedSquareQ₂_eq_two_of_even hd, shiftedSquareD₀]
    exact Nat.mul_div_cancel' hd.two_dvd
  · simp [shiftedSquareQ₂_eq_one_of_not_even hd, shiftedSquareD₀]

/-- Positivity survives the parity quotient. -/
theorem shiftedSquareD₀_pos {d : ℕ} (hd : 0 < d) :
    0 < shiftedSquareD₀ d := by
  have hproduct : 0 < shiftedSquareQ₂ d * shiftedSquareD₀ d := by
    simpa only [shiftedSquareQ₂_mul_D₀] using hd
  by_contra hnot
  have hzero : shiftedSquareD₀ d = 0 := Nat.eq_zero_of_not_pos hnot
  simp [hzero] at hproduct

@[simp] theorem shiftedSquareZeta_re (a : ℤ) (d n : ℕ) :
    (shiftedSquareZeta a d n).re =
      (n : ℚ) / (shiftedSquareQ₂ d : ℚ) := rfl

@[simp] theorem shiftedSquareZeta_im (a : ℤ) (d n : ℕ) :
    (shiftedSquareZeta a d n).im =
      1 / (shiftedSquareQ₂ d : ℚ) := rfl

/-- The coordinate representation is exactly scalar division of
`n + omega` by the nonzero rational scalar `q₂`. -/
theorem shiftedSquareZeta_eq_inv_smul (a : ℤ) (d n : ℕ) :
    shiftedSquareZeta a d n =
      ((shiftedSquareQ₂ d : ℚ)⁻¹) •
        (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
          QuadraticAlgebra.omega) := by
  ext
  · change
      (n : ℚ) / (shiftedSquareQ₂ d : ℚ) =
        (shiftedSquareQ₂ d : ℚ)⁻¹ * ((n : ℚ) + 0)
    rw [div_eq_mul_inv]
    ring
  · change
      1 / (shiftedSquareQ₂ d : ℚ) =
        (shiftedSquareQ₂ d : ℚ)⁻¹ * (0 + 1)
    simp [div_eq_mul_inv]

/-- A squarefree shift makes the source coordinates primitive. -/
theorem shiftedSquareQuadratic_coprime
    {a : ℤ} {d w n : ℕ} (ha : Squarefree a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    d.Coprime n :=
  shiftedSquare_coprime_of_squarefree_shift ha heq

/-- If the parity factor is two, primitivity forces `n` to be odd. -/
theorem shiftedSquare_n_odd_of_even_d
    {a : ℤ} {d w n : ℕ} (ha : Squarefree a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (hdEven : Even d) : Odd n := by
  have hcoprime : d.Coprime n :=
    shiftedSquareQuadratic_coprime ha heq
  have htwoCoprime : Nat.Coprime 2 n :=
    Nat.Coprime.of_dvd_left hdEven.two_dvd hcoprime
  simpa using htwoCoprime

/-- In the even branch, the radicand has the required residue modulo four. -/
theorem shiftedSquare_radicand_modEq_one_of_even_d
    {a : ℤ} {d w n : ℕ} (ha : Squarefree a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (hdEven : Even d) : (-a : ℤ) ≡ 1 [ZMOD 4] := by
  obtain ⟨k, hdk⟩ := even_iff_exists_two_mul.mp hdEven
  obtain ⟨l, hnl⟩ :=
    (shiftedSquare_n_odd_of_even_d ha heq hdEven).exists_bit1
  have hdkInt : (d : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hdk
  have hnlInt : (n : ℤ) = 2 * (l : ℤ) + 1 := by exact_mod_cast hnl
  have haIdentity : a = (d : ℤ) ^ 2 * (w : ℤ) - (n : ℤ) ^ 2 := by
    linarith
  rw [Int.modEq_iff_dvd]
  refine ⟨(k : ℤ) ^ 2 * (w : ℤ) - ((l : ℤ) ^ 2 + (l : ℤ)), ?_⟩
  rw [haIdentity, hdkInt, hnlInt]
  ring

/-- Negating an integer shift preserves squarefreeness. -/
theorem shiftedSquare_radicand_squarefree {a : ℤ} (ha : Squarefree a) :
    Squarefree (-a) := by
  exact ((Associated.refl a).neg_left.squarefree_iff).2 ha

/-- A squarefree shift other than `-1` gives a nonsquare radicand `-a`. -/
theorem shiftedSquare_radicand_not_isSquare
    {a : ℤ} (ha : Squarefree a) (haNegOne : a ≠ -1) :
    ¬ IsSquare (-a) := by
  intro hsquare
  obtain ⟨r, hr⟩ := hsquare
  have hrDvd : r * r ∣ -a := by rw [hr]
  have hrUnit : IsUnit r := shiftedSquare_radicand_squarefree ha r hrDvd
  have hrSq : r ^ 2 = 1 := Int.isUnit_sq hrUnit
  apply haNegOne
  calc
    a = -(-a) := by ring
    _ = -(r * r) := by rw [hr]
    _ = -1 := by simpa only [pow_two] using congrArg Neg.neg hrSq

/-- Consequently `X^2-(-a)` has no rational root, supplying Mathlib's
quadratic-field certificate. -/
theorem shiftedSquare_radicand_noRationalRoot
    {a : ℤ} (ha : Squarefree a) (haNegOne : a ≠ -1) :
    rationalQuadraticAlgebraNoRationalRoot (-a) :=
  rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare (-a)
    (shiftedSquare_radicand_not_isSquare ha haNegOne)

/-- The rational trace of `ζ` is the displayed integral trace. -/
theorem shiftedSquareZeta_trace (a : ℤ) (d n : ℕ) :
    QuadraticAlgebra.trace (shiftedSquareZeta a d n) =
      (shiftedSquareZetaTrace d n : ℚ) := by
  rw [QuadraticAlgebra.trace_def]
  by_cases hdEven : Even d
  · simp [shiftedSquareZeta, shiftedSquareZetaTrace, shiftedSquareQ₂,
      hdEven]
    ring
  · simp [shiftedSquareZeta, shiftedSquareZetaTrace, shiftedSquareQ₂,
      hdEven]

/-- The quadratic-algebra norm of `ζ` is exactly `d₀^2 w`. -/
theorem shiftedSquareZeta_quadraticNorm
    {a : ℤ} {d w n : ℕ}
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    QuadraticAlgebra.norm (shiftedSquareZeta a d n) =
      ((shiftedSquareD₀ d) ^ 2 * w : ℕ) := by
  let q : ℕ := shiftedSquareQ₂ d
  let d₀ : ℕ := shiftedSquareD₀ d
  have hqPos : 0 < q := by simpa only [q] using shiftedSquareQ₂_pos d
  have hqRatNe : (q : ℚ) ≠ 0 := by exact_mod_cast hqPos.ne'
  have hqdNat : q * d₀ = d := by
    simpa only [q, d₀] using shiftedSquareQ₂_mul_D₀ d
  have hqdRat : (q : ℚ) * (d₀ : ℚ) = (d : ℚ) := by
    exact_mod_cast hqdNat
  have heqRat : (d : ℚ) ^ 2 * (w : ℚ) = (n : ℚ) ^ 2 + (a : ℚ) := by
    exact_mod_cast heq
  rw [QuadraticAlgebra.norm_def]
  change
    (n : ℚ) / (q : ℚ) * ((n : ℚ) / (q : ℚ)) +
          0 * ((n : ℚ) / (q : ℚ)) * (1 / (q : ℚ)) -
        ((-a : ℤ) : ℚ) * (1 / (q : ℚ)) * (1 / (q : ℚ)) =
      ((d₀ ^ 2 * w : ℕ) : ℚ)
  calc
    (n : ℚ) / (q : ℚ) * ((n : ℚ) / (q : ℚ)) +
          0 * ((n : ℚ) / (q : ℚ)) * (1 / (q : ℚ)) -
        ((-a : ℤ) : ℚ) * (1 / (q : ℚ)) * (1 / (q : ℚ)) =
        ((n : ℚ) ^ 2 + (a : ℚ)) / (q : ℚ) ^ 2 := by
      push_cast
      field_simp [hqRatNe]
      ring
    _ = ((d : ℚ) ^ 2 * (w : ℚ)) / (q : ℚ) ^ 2 := by
      rw [heqRat]
    _ = ((d₀ ^ 2 * w : ℕ) : ℚ) := by
      rw [← hqdRat]
      push_cast
      field_simp [hqRatNe]

/-- The same exact identity for the canonical rational algebra norm. -/
theorem shiftedSquareZeta_algebraNorm
    {a : ℤ} {d w n : ℕ}
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    (Algebra.norm ℚ) (shiftedSquareZeta a d n) =
      ((shiftedSquareD₀ d) ^ 2 * w : ℕ) := by
  rw [rationalQuadraticAlgebra_norm_apply]
  simpa only [QuadraticAlgebra.norm_def, zero_mul, add_zero] using
    shiftedSquareZeta_quadraticNorm heq

/-- The normalized element is integral over `ℤ`.  Its monic characteristic
polynomial has the integral trace above and constant term `d₀^2 w`. -/
theorem shiftedSquareZeta_isIntegral
    {a : ℤ} {d w n : ℕ}
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    IsIntegral ℤ (shiftedSquareZeta a d n) := by
  let P : Polynomial ℤ :=
    Polynomial.X ^ 2 -
        Polynomial.C (shiftedSquareZetaTrace d n : ℤ) * Polynomial.X +
      Polynomial.C (((shiftedSquareD₀ d) ^ 2 * w : ℕ) : ℤ)
  refine ⟨P, ?_, ?_⟩
  · dsimp [P]
    monicity <;> norm_num
  · have hchar :=
      QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero
        (shiftedSquareZeta a d n)
    rw [shiftedSquareZeta_trace,
      shiftedSquareZeta_quadraticNorm heq] at hchar
    have htraceCast :
        (algebraMap ℚ (rationalQuadraticAlgebra (-a)))
            (shiftedSquareZetaTrace d n : ℚ) =
          ((shiftedSquareZetaTrace d n : ℤ) :
            rationalQuadraticAlgebra (-a)) := by
      norm_num
    have hnormCast :
        (algebraMap ℚ (rationalQuadraticAlgebra (-a)))
            (((shiftedSquareD₀ d) ^ 2 * w : ℕ) : ℚ) =
          ((((shiftedSquareD₀ d) ^ 2 * w : ℕ) : ℤ) :
            rationalQuadraticAlgebra (-a)) := by
      norm_num
    have hnormExpanded :
        ((((shiftedSquareD₀ d) ^ 2 * w : ℕ) : ℤ) :
            rationalQuadraticAlgebra (-a)) =
          (shiftedSquareD₀ d : rationalQuadraticAlgebra (-a)) ^ 2 *
            (w : rationalQuadraticAlgebra (-a)) := by
      norm_num
    rw [Algebra.smul_def, htraceCast, hnormCast, hnormExpanded] at hchar
    dsimp [P]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    simpa only [map_mul, map_pow, map_natCast, Int.cast_natCast,
      Nat.cast_pow, Nat.cast_mul] using hchar

/-- Complete elementary package at the start of
`L:square-map-coordinates`. -/
theorem shiftedSquareQuadraticInteger_package
    {a : ℤ} {d w n : ℕ}
    (ha : Squarefree a) (ha0 : a ≠ 0) (haNegOne : a ≠ -1)
    (hd : 0 < d) (hw : 0 < w) (hn : 0 < n)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    0 < d ∧ 0 < w ∧ 0 < n ∧
      d.Coprime n ∧
      shiftedSquareQ₂ d * shiftedSquareD₀ d = d ∧
      0 < shiftedSquareD₀ d ∧
      (-a : ℤ) ≠ 0 ∧
      Squarefree (-a) ∧
      ¬ IsSquare (-a) ∧
      rationalQuadraticAlgebraNoRationalRoot (-a) ∧
      (Even d → Odd n ∧ (-a : ℤ) ≡ 1 [ZMOD 4]) ∧
      IsIntegral ℤ (shiftedSquareZeta a d n) ∧
      (Algebra.norm ℚ) (shiftedSquareZeta a d n) =
        ((shiftedSquareD₀ d) ^ 2 * w : ℕ) := by
  refine ⟨hd, hw, hn, shiftedSquareQuadratic_coprime ha heq,
    shiftedSquareQ₂_mul_D₀ d, shiftedSquareD₀_pos hd, ?_,
    shiftedSquare_radicand_squarefree ha,
    shiftedSquare_radicand_not_isSquare ha haNegOne,
    shiftedSquare_radicand_noRationalRoot ha haNegOne, ?_,
    shiftedSquareZeta_isIntegral heq,
    shiftedSquareZeta_algebraNorm heq⟩
  · simpa only [neg_ne_zero] using ha0
  · intro hdEven
    exact ⟨shiftedSquare_n_odd_of_even_d ha heq hdEven,
      shiftedSquare_radicand_modEq_one_of_even_d ha heq hdEven⟩

/-- A member of an exact squarefree shifted-square block supplies all source
hypotheses for the quadratic-integer package. -/
theorem shiftedSquareQuadraticInteger_package_of_mem
    {a : ℤ} {D Y N d w n : ℕ}
    (ha : Squarefree a) (ha0 : a ≠ 0) (haNegOne : a ≠ -1)
    (hp : (d, w, n) ∈ squarefreeShiftedSquareBlock a D Y N) :
    0 < d ∧ 0 < w ∧ 0 < n ∧
      d.Coprime n ∧
      shiftedSquareQ₂ d * shiftedSquareD₀ d = d ∧
      0 < shiftedSquareD₀ d ∧
      (-a : ℤ) ≠ 0 ∧
      Squarefree (-a) ∧
      ¬ IsSquare (-a) ∧
      rationalQuadraticAlgebraNoRationalRoot (-a) ∧
      (Even d → Odd n ∧ (-a : ℤ) ≡ 1 [ZMOD 4]) ∧
      IsIntegral ℤ (shiftedSquareZeta a d n) ∧
      (Algebra.norm ℚ) (shiftedSquareZeta a d n) =
        ((shiftedSquareD₀ d) ^ 2 * w : ℕ) := by
  have hp' := mem_squarefreeShiftedSquareBlock.mp hp
  exact shiftedSquareQuadraticInteger_package ha ha0 haNegOne
    hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2.2.2.2.2.2.2.1

end

end PellPaper
