import Pell.ShiftedSquareMinkowskiEmbeddingBox
import Pell.ShiftedSquareMinkowskiC0Nu
import Pell.ShiftedSquareFieldDiscriminantBound
import Mathlib.Tactic

/-!
# Simultaneous Minkowski embeddings with the attached C₀--nu package

This isolated candidate keeps the simultaneous-box Minkowski element and
builds all subsequent ideal and factorization data from that same element.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

local instance shiftedSquareMinkowskiEmbeddingC₀Nu_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- In a quadratic number field, a simultaneous upper bound at all infinite
places bounds the absolute rational norm by the square of that bound. -/
theorem quadratic_absNorm_le_sq_of_infinitePlace_lt
    (K : Type*) [Field K] [NumberField K]
    (hrank : Module.finrank ℚ K = 2)
    (mu : NumberField.RingOfIntegers K) (B : ℝ)
    (hplace : ∀ v : NumberField.InfinitePlace K, v mu < B) :
    ((|Algebra.norm ℚ (mu : K)| : ℚ) : ℝ) ≤ B ^ 2 := by
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm]
  calc
    ∏ v : NumberField.InfinitePlace K,
          v (mu : K) ^ NumberField.InfinitePlace.mult v ≤
        ∏ v : NumberField.InfinitePlace K,
          B ^ NumberField.InfinitePlace.mult v := by
      refine Finset.prod_le_prod (fun v _ => ?_) (fun v _ => ?_)
      · exact pow_nonneg (apply_nonneg v _) _
      · exact pow_le_pow_left₀
          (apply_nonneg v _) (hplace v).le _
    _ = B ^ (∑ v : NumberField.InfinitePlace K,
          NumberField.InfinitePlace.mult v) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = B ^ 2 := by
      rw [NumberField.InfinitePlace.sum_mult_eq, hrank]

/-- The norm bound obtained by multiplying the simultaneous shifted-square
embedding bounds.  This theorem keeps the particular `mu` supplied by the
caller. -/
theorem shiftedSquare_mu_absNorm_le_sixteen_mul_sqrt_discr_of_embedding_lt
    {a : ℤ} {d : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
    (hplace :
      ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
        v mu <
          4 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) *
              Real.sqrt
                |NumberField.discr (rationalQuadraticAlgebra (-a))|)) :
    ((|Algebra.norm ℚ
        (mu : rationalQuadraticAlgebra (-a))| : ℚ) : ℝ) ≤
      16 * (shiftedSquareD₀ d : ℝ) *
        Real.sqrt
          |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
  let X : ℝ :=
    (shiftedSquareD₀ d : ℝ) *
      Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))|
  have hX : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hrank : Module.finrank ℚ (rationalQuadraticAlgebra (-a)) = 2 := by
    exact QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0
  calc
    ((|Algebra.norm ℚ
          (mu : rationalQuadraticAlgebra (-a))| : ℚ) : ℝ) ≤
        (4 * Real.sqrt X) ^ 2 :=
      quadratic_absNorm_le_sq_of_infinitePlace_lt
        (rationalQuadraticAlgebra (-a)) hrank mu (4 * Real.sqrt X)
        (by simpa only [X] using hplace)
    _ = 16 * (shiftedSquareD₀ d : ℝ) *
          Real.sqrt
            |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
      rw [mul_pow, Real.sq_sqrt hX]
      dsimp only [X]
      norm_num
      ring

/-- Divide the preceding norm estimate by the positive ideal norm `d₀`.
The conclusion concerns the `C₀` defined from the very same `mu`. -/
theorem shiftedSquareC₀_le_sixteen_mul_sqrt_discr_of_embedding_lt
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    {mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    (hmu : mu ∈ shiftedSquareIdealDivisor heq)
    (hplace :
      ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
        v mu <
          4 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) *
              Real.sqrt
                |NumberField.discr (rationalQuadraticAlgebra (-a))|)) :
    (shiftedSquareC₀ (d := d) mu : ℝ) ≤
      16 * Real.sqrt
        |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
  have hnorm :=
    shiftedSquare_mu_absNorm_le_sixteen_mul_sqrt_discr_of_embedding_lt
      mu hplace
  have hnormQ := shiftedSquare_mu_rationalNorm_abs ha heq hmu
  have hnormR := congrArg (fun q : ℚ => (q : ℝ)) hnormQ
  have hd₀R : (0 : ℝ) < shiftedSquareD₀ d := by
    exact_mod_cast shiftedSquareD₀_pos hd
  apply (mul_le_mul_iff_of_pos_left hd₀R).mp
  calc
    (shiftedSquareD₀ d : ℝ) *
          (shiftedSquareC₀ (d := d) mu : ℝ) =
        ((((shiftedSquareD₀ d *
          shiftedSquareC₀ (d := d) mu : ℕ) : ℚ)) : ℝ) := by
      norm_num
    _ = ((|Algebra.norm ℚ
          (mu : rationalQuadraticAlgebra (-a))| : ℚ) : ℝ) := by
      rw [hnormR]
    _ ≤ 16 * (shiftedSquareD₀ d : ℝ) *
          Real.sqrt
            |NumberField.discr (rationalQuadraticAlgebra (-a))| := hnorm
    _ = (shiftedSquareD₀ d : ℝ) *
          (16 * Real.sqrt
            |NumberField.discr (rationalQuadraticAlgebra (-a))|) := by
      ring

/-- Convert the discriminant-radius simultaneous estimate to the
route-facing absolute-shift radius, without choosing another element. -/
theorem shiftedSquare_embedding_lt_eight_mul_sqrt_abs_of_lt_four_discr
    {a : ℤ} {d : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    (hplace :
      ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
        v mu <
          4 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) *
              Real.sqrt
                |NumberField.discr (rationalQuadraticAlgebra (-a))|)) :
    ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      v mu <
        8 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|) := by
  intro v
  refine (hplace v).trans_le ?_
  have hdisc :=
    sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a
  have hd₀ : 0 ≤ (shiftedSquareD₀ d : ℝ) := by positivity
  let X : ℝ := (shiftedSquareD₀ d : ℝ) * Real.sqrt |a|
  have hX : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hinside :
      (shiftedSquareD₀ d : ℝ) *
          Real.sqrt
            |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
        4 * X := by
    calc
      (shiftedSquareD₀ d : ℝ) *
            Real.sqrt
              |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
          (shiftedSquareD₀ d : ℝ) * (2 * Real.sqrt |a|) :=
        mul_le_mul_of_nonneg_left hdisc hd₀
      _ = 2 * X := by dsimp only [X]; ring
      _ ≤ 4 * X := by nlinarith
  calc
    4 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) *
            Real.sqrt
              |NumberField.discr (rationalQuadraticAlgebra (-a))|) ≤
        4 * Real.sqrt (4 * X) := by
      gcongr
    _ = 8 * Real.sqrt X := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring
    _ = 8 * Real.sqrt
        ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|) := by rfl

/-! ## The same-element package -/

/-- The simultaneous embedding witness and all `C₀`--`nu` consequences
constructed from that exact witness. -/
structure ShiftedSquareMinkowskiEmbeddingC₀NuPackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) where
  mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  C₀ : ℕ
  nu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  Q : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
  mu_mem : mu ∈ shiftedSquareIdealDivisor heq
  mu_ne_zero : mu ≠ 0
  embedding_lt_discr :
    ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      v mu <
        4 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) *
            Real.sqrt
              |NumberField.discr (rationalQuadraticAlgebra (-a))|)
  embedding_lt_abs :
    ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
      v mu <
        8 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)
  C₀_pos : 0 < C₀
  mu_norm :
    |Algebra.norm ℚ (mu : rationalQuadraticAlgebra (-a))| =
      ((shiftedSquareD₀ d * C₀ : ℕ) : ℚ)
  mu_norm_le_sixteen_mul_sqrt_discr :
    ((|Algebra.norm ℚ
        (mu : rationalQuadraticAlgebra (-a))| : ℚ) : ℝ) ≤
      16 * (shiftedSquareD₀ d : ℝ) *
        Real.sqrt
          |NumberField.discr (rationalQuadraticAlgebra (-a))|
  factorization :
    mu ^ 2 * nu =
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ^ 2 *
        shiftedSquareZetaInteger heq
  nu_norm : Algebra.norm ℤ nu = ((w * C₀ ^ 2 : ℕ) : ℤ)
  C₀_le_sixteen_mul_sqrt_discr :
    (C₀ : ℝ) ≤
      16 * Real.sqrt
        |NumberField.discr (rationalQuadraticAlgebra (-a))|
  C₀_le_thirtytwo_mul_sqrt_abs :
    (C₀ : ℝ) ≤ 32 * Real.sqrt |a|
  mu_principal_eq_ideal_mul_Q :
    Ideal.span {mu} = shiftedSquareIdealDivisor heq * Q
  Q_absNorm : Ideal.absNorm Q = C₀
  C₀_ideal_mul_le_mu_principal :
    Ideal.span
        {(C₀ : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a)))} *
      shiftedSquareIdealDivisor heq ≤ Ideal.span {mu}

/-- The simultaneous-box element admits the full integral `C₀`--`nu`
factorization, ideal quotient, and explicit `C₀` bounds without changing
the chosen `mu`. -/
theorem exists_shiftedSquareMinkowskiEmbeddingC₀Nu_package
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    Nonempty (ShiftedSquareMinkowskiEmbeddingC₀NuPackage heq) := by
  obtain ⟨mu, hmu, hmu0, hplace⟩ :=
    exists_shiftedSquareIdealDivisor_minkowskiEmbeddingBox ha hd heq
  let C₀ := shiftedSquareC₀ (d := d) mu
  obtain ⟨Q, hQ, hQnorm, hCI⟩ :=
    exists_shiftedSquareC₀_quotientIdeal ha hd heq hmu
  obtain ⟨nu, hnu⟩ := exists_shiftedSquareNu ha hd heq hmu
  have hC₀pos : 0 < C₀ :=
    shiftedSquareC₀_pos ha hd heq hmu hmu0
  have hmuNorm :
      |Algebra.norm ℚ (mu : rationalQuadraticAlgebra (-a))| =
        ((shiftedSquareD₀ d * C₀ : ℕ) : ℚ) :=
    shiftedSquare_mu_rationalNorm_abs ha heq hmu
  have hmuNormBound :=
    shiftedSquare_mu_absNorm_le_sixteen_mul_sqrt_discr_of_embedding_lt
      mu hplace
  have hC₀disc :=
    shiftedSquareC₀_le_sixteen_mul_sqrt_discr_of_embedding_lt
      ha hd heq hmu hplace
  have hplaceAbs :=
    shiftedSquare_embedding_lt_eight_mul_sqrt_abs_of_lt_four_discr hplace
  have hC₀abs : (C₀ : ℝ) ≤ 32 * Real.sqrt |a| := by
    refine hC₀disc.trans ?_
    have hdisc :=
      sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a
    calc
      16 * Real.sqrt
            |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
          16 * (2 * Real.sqrt |a|) := by gcongr
      _ = 32 * Real.sqrt |a| := by ring
  refine ⟨{
    mu := mu
    C₀ := C₀
    nu := nu
    Q := Q
    mu_mem := hmu
    mu_ne_zero := hmu0
    embedding_lt_discr := hplace
    embedding_lt_abs := hplaceAbs
    C₀_pos := hC₀pos
    mu_norm := hmuNorm
    mu_norm_le_sixteen_mul_sqrt_discr := hmuNormBound
    factorization := hnu
    nu_norm := shiftedSquareNu_algebraNorm ha hd heq hmu hmu0 hnu
    C₀_le_sixteen_mul_sqrt_discr := hC₀disc
    C₀_le_thirtytwo_mul_sqrt_abs := hC₀abs
    mu_principal_eq_ideal_mul_Q := hQ
    Q_absNorm := hQnorm
    C₀_ideal_mul_le_mu_principal := hCI }⟩

end

end PellPaper
