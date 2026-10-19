import Pell.ShiftedSquareAuxiliarySurfaceLevelWeight
import Pell.Main3LargeAnalyticBlockAuxiliaryPartition
import Mathlib.Tactic

/-!
# Workspace: weighted sums over the Main3 auxiliary-key gate

The manuscript's three scalar sums are bounded here by the simplest route
needed downstream: every exact key has `1 <= ell` and `C₀ <= R`, so the
weights `C₀/ell` and `(C₀/ell)^(3/2)` are at most `R` and `R^(3/2)`.
Combining these pointwise estimates with the already-proved subpower key-count
bound gives the genuine powers `R`, `R^2`, and `R^(5/2)`.  Since the Main3
gate has `R = ceil (32 sqrt |a|)`, the last power is `A_a^(5/4)` up to an
absolute factor; multiplication by the two discriminant factors
`A_a^(-3/8)` and `A_a^(-1/8)` yields the paper's `A_a^(7/8)` and
`A_a^(9/8)` powers.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Exact range and denominator positivity supplied by membership in the
literal scalar auxiliary-key gate. -/
theorem shiftedSquareAuxiliaryKey_range_and_denominator_pos
    {R : ℕ} {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ shiftedSquareAuxiliaryKeys R) :
    1 ≤ key.C₀ ∧ key.C₀ ≤ R ∧ 1 ≤ key.r ∧ 1 ≤ key.ell := by
  simp only [shiftedSquareAuxiliaryKeys, Finset.mem_biUnion,
    Finset.mem_image] at hkey
  obtain ⟨C₀, hC₀, bζ, hbζ, p, hp, rfl⟩ := hkey
  rcases p with ⟨r, ell⟩
  have hC₀range := Finset.mem_Icc.mp hC₀
  have hbζCases : bζ = 1 ∨ bζ = 2 := mem_shiftedSquareBζValues.mp hbζ
  have hbζAbsPos : 0 < bζ.natAbs := by
    rcases hbζCases with rfl | rfl <;> norm_num
  have hnumPos : 0 < C₀ ^ 2 * bζ.natAbs :=
    Nat.mul_pos (pow_pos hC₀range.1 2) hbζAbsPos
  have hpData :=
    (mem_specialParabolaDenominatorPairs_iff hnumPos.ne').mp hp
  exact ⟨hC₀range.1, hC₀range.2, hpData.1, hpData.2.1⟩

/-- The real manuscript weight `C₀/ell` lies in `[0,R]` on the exact key
gate. -/
theorem shiftedSquareAuxiliaryKey_ratio_nonneg_and_le
    {R : ℕ} {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ shiftedSquareAuxiliaryKeys R) :
    0 ≤ (key.C₀ : ℝ) / (key.ell : ℝ) ∧
      (key.C₀ : ℝ) / (key.ell : ℝ) ≤ (R : ℝ) := by
  have hdata := shiftedSquareAuxiliaryKey_range_and_denominator_pos hkey
  have hell : (1 : ℝ) ≤ key.ell := by exact_mod_cast hdata.2.2.2
  have hC₀R : (key.C₀ : ℝ) ≤ R := by exact_mod_cast hdata.2.1
  constructor
  · positivity
  · exact (div_le_self (by positivity) hell).trans hC₀R

/-- The sharp Main3 ceiling is at most an absolute constant times the square
root of the manuscript shift weight `A_a = 2|a|`.  This is the bridge turning
the powers of `R` below into powers of `A_a`. -/
theorem main3LargeAnalytic_auxiliaryC₀Ceiling_le_thirtythree_mul_sqrt_shiftWeight
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ≤
      33 * Real.sqrt (2 * |(shiftedSquareA h v : ℝ)|) := by
  have hiActive :=
    (mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi).1
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiActive
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
      hiBroad hcell
  have ha0 : shiftedSquareA h v ≠ 0 := hshift.2.2.1
  have haNat : 1 ≤ (shiftedSquareA h v).natAbs :=
    (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha0))
  have haAbs : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
    have haInt : (1 : ℤ) ≤ |shiftedSquareA h v| := by
      have haIntNat : (1 : ℤ) ≤
          ((shiftedSquareA h v).natAbs : ℤ) := by
        exact_mod_cast haNat
      simpa only [Int.abs_eq_natAbs] using haIntNat
    exact_mod_cast haInt
  have hsqrtOne : (1 : ℝ) ≤
      Real.sqrt |(shiftedSquareA h v : ℝ)| := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt haAbs
  have hceil := (main3LargeAnalytic_auxiliaryC₀Ceiling_spec h v).2
  have hfirst : (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ≤
      33 * Real.sqrt |(shiftedSquareA h v : ℝ)| := by
    linarith
  have hsqrtMono : Real.sqrt |(shiftedSquareA h v : ℝ)| ≤
      Real.sqrt (2 * |(shiftedSquareA h v : ℝ)|) := by
    apply Real.sqrt_le_sqrt
    nlinarith [abs_nonneg (shiftedSquareA h v : ℝ)]
  exact hfirst.trans (mul_le_mul_of_nonneg_left hsqrtMono (by norm_num))

/-- Any nonnegative power of the Main3 auxiliary ceiling has the expected
half-power dependence on `A_a = 2|a|`. -/
theorem main3LargeAnalytic_auxiliaryC₀Ceiling_rpow_le_shiftWeight
    {theta p : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : 0 ≤ p) :
    (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ^ p ≤
      33 ^ p *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ (p / 2) := by
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR :=
    main3LargeAnalytic_auxiliaryC₀Ceiling_le_thirtythree_mul_sqrt_shiftWeight hi
  calc
    (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ^ p ≤
        (33 * Real.sqrt A) ^ p :=
      Real.rpow_le_rpow (by positivity) (by simpa only [A] using hR) hp
    _ = 33 ^ p * (Real.sqrt A) ^ p := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg A)]
    _ = 33 ^ p * A ^ (p / 2) := by
      rw [show Real.sqrt A = A ^ ((1 : ℝ) / 2) by
        exact Real.sqrt_eq_rpow A,
        ← Real.rpow_mul hA]
      congr 2
      ring

/-- The auxiliary gate's subpower base `2R²` is likewise bounded by an
absolute multiple of `A_a`. -/
theorem main3LargeAnalytic_auxiliarySurfaceBudget_rpow_le_shiftWeight
    {theta ε : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hε : 0 ≤ ε) :
    (((2 * (main3LargeAnalytic_auxiliaryC₀Ceiling h v) ^ 2 : ℕ) : ℝ) ^ ε) ≤
      (2178 : ℝ) ^ ε *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ ε := by
  let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hRtwoRaw :=
    main3LargeAnalytic_auxiliaryC₀Ceiling_rpow_le_shiftWeight
      (p := (2 : ℝ)) hi (by norm_num)
  have hRtwo : (R : ℝ) ^ 2 ≤ 1089 * A := by
    norm_num [Real.rpow_two, Real.rpow_one] at hRtwoRaw ⊢
    simpa only [R, A] using hRtwoRaw
  have hbudget : ((2 * R ^ 2 : ℕ) : ℝ) ≤ 2178 * A := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    calc
      2 * (R : ℝ) ^ 2 ≤ 2 * (1089 * A) :=
        mul_le_mul_of_nonneg_left hRtwo (by norm_num)
      _ = 2178 * A := by ring
  calc
    (((2 * R ^ 2 : ℕ) : ℝ) ^ ε) ≤ (2178 * A) ^ ε :=
      Real.rpow_le_rpow (by positivity) hbudget hε
    _ = (2178 : ℝ) ^ ε * A ^ ε := by
      rw [Real.mul_rpow (by norm_num) hA]

/-- Combined transfer: `R^q (2R²)^ε` becomes
`33^q 2178^ε A_a^(q/2+ε)`. -/
theorem main3LargeAnalytic_auxiliaryPowerBudget_le_shiftWeight
    {theta q ε : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ^ q *
        (((2 * (main3LargeAnalytic_auxiliaryC₀Ceiling h v) ^ 2 : ℕ) : ℝ) ^ ε) ≤
      33 ^ q * 2178 ^ ε *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ (q / 2 + ε) := by
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hR := main3LargeAnalytic_auxiliaryC₀Ceiling_rpow_le_shiftWeight
    hi hq
  have hbudget :=
    main3LargeAnalytic_auxiliarySurfaceBudget_rpow_le_shiftWeight hi hε
  have hApos : 0 < A := by
    have hRone : (1 : ℝ) ≤
        main3LargeAnalytic_auxiliaryC₀Ceiling h v := by
      exact_mod_cast main3LargeAnalytic_one_le_auxiliaryC₀Ceiling hi
    have hRbound :=
      main3LargeAnalytic_auxiliaryC₀Ceiling_le_thirtythree_mul_sqrt_shiftWeight hi
    have hRbound' :
        (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ≤
          33 * Real.sqrt A := by
      simpa only [A] using hRbound
    have hsqrtPos : 0 < Real.sqrt A := by
      nlinarith [hRbound']
    exact (Real.sqrt_pos).mp hsqrtPos
  calc
    (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ^ q *
        (((2 * (main3LargeAnalytic_auxiliaryC₀Ceiling h v) ^ 2 : ℕ) : ℝ) ^ ε) ≤
      (33 ^ q * A ^ (q / 2)) * (2178 ^ ε * A ^ ε) := by
        apply mul_le_mul hR (by simpa only [A] using hbudget)
        · positivity
        · positivity
    _ = 33 ^ q * 2178 ^ ε * A ^ (q / 2 + ε) := by
      rw [Real.rpow_add hApos]
      ring
    _ = 33 ^ q * 2178 ^ ε *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ (q / 2 + ε) := by
      rfl

/-- A single constant simultaneously controls the three key sums used in the
outer Main3 estimate.  The remaining factor is the already-established
arbitrarily small power of the maximal surface-level numerator. -/
theorem exists_pos_shiftedSquareAuxiliaryKey_weightedSums_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
      (∑ _key ∈ shiftedSquareAuxiliaryKeys R, (1 : ℝ)) ≤
          2 * C * (R : ℝ) * ((2 * R ^ 2 : ℕ) : ℝ) ^ ε ∧
      (∑ key ∈ shiftedSquareAuxiliaryKeys R,
          (key.C₀ : ℝ) / (key.ell : ℝ)) ≤
          2 * C * (R : ℝ) ^ 2 *
            ((2 * R ^ 2 : ℕ) : ℝ) ^ ε ∧
      (∑ key ∈ shiftedSquareAuxiliaryKeys R,
          ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ ((3 : ℝ) / 2)) ≤
          2 * C * (R : ℝ) ^ ((5 : ℝ) / 2) *
            ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC, hcard⟩ :=
    exists_pos_card_shiftedSquareAuxiliaryKeys_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hRnonneg : (0 : ℝ) ≤ R := hRpos.le
  have hcard' : ((shiftedSquareAuxiliaryKeys R).card : ℝ) ≤
      2 * C * (R : ℝ) * Z ^ ε := by
    simpa only [Z] using hcard R hR
  have hratio (key : ShiftedSquareAuxiliaryKey)
      (hkey : key ∈ shiftedSquareAuxiliaryKeys R) :
      (key.C₀ : ℝ) / (key.ell : ℝ) ≤ (R : ℝ) :=
    (shiftedSquareAuxiliaryKey_ratio_nonneg_and_le hkey).2
  have hratioPow (key : ShiftedSquareAuxiliaryKey)
      (hkey : key ∈ shiftedSquareAuxiliaryKeys R) :
      ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ ((3 : ℝ) / 2) ≤
        (R : ℝ) ^ ((3 : ℝ) / 2) := by
    exact Real.rpow_le_rpow
      (shiftedSquareAuxiliaryKey_ratio_nonneg_and_le hkey).1
      (hratio key hkey) (by norm_num)
  constructor
  · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Z] using hcard'
  constructor
  · calc
      (∑ key ∈ shiftedSquareAuxiliaryKeys R,
          (key.C₀ : ℝ) / (key.ell : ℝ)) ≤
          ∑ _key ∈ shiftedSquareAuxiliaryKeys R, (R : ℝ) := by
        exact Finset.sum_le_sum fun key hkey => hratio key hkey
      _ = ((shiftedSquareAuxiliaryKeys R).card : ℝ) * (R : ℝ) := by
        simp
      _ ≤ (2 * C * (R : ℝ) * Z ^ ε) * (R : ℝ) :=
        mul_le_mul_of_nonneg_right hcard' hRnonneg
      _ = 2 * C * (R : ℝ) ^ 2 *
          ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
        dsimp only [Z]
        ring
  · calc
      (∑ key ∈ shiftedSquareAuxiliaryKeys R,
          ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ ((3 : ℝ) / 2)) ≤
          ∑ _key ∈ shiftedSquareAuxiliaryKeys R,
            (R : ℝ) ^ ((3 : ℝ) / 2) := by
        exact Finset.sum_le_sum fun key hkey => hratioPow key hkey
      _ = ((shiftedSquareAuxiliaryKeys R).card : ℝ) *
          (R : ℝ) ^ ((3 : ℝ) / 2) := by
        simp
      _ ≤ (2 * C * (R : ℝ) * Z ^ ε) *
          (R : ℝ) ^ ((3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hcard'
          (Real.rpow_nonneg hRnonneg _)
      _ = 2 * C * (R : ℝ) ^ ((5 : ℝ) / 2) *
          ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
        rw [show (5 : ℝ) / 2 = 1 + 3 / 2 by norm_num,
          Real.rpow_add hRpos, Real.rpow_one]
        dsimp only [Z]
        ring

/-- Direct specialization of the three generic weighted bounds to the
literal Main3 block gate. -/
theorem exists_pos_main3LargeAnalytic_blockAuxiliaryKeyGate_weightedSums_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
        (∑ _key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            (1 : ℝ)) ≤
              2 * C * (R : ℝ) * ((2 * R ^ 2 : ℕ) : ℝ) ^ ε ∧
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            (key.C₀ : ℝ) / (key.ell : ℝ)) ≤
              2 * C * (R : ℝ) ^ 2 *
                ((2 * R ^ 2 : ℕ) : ℝ) ^ ε ∧
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ ((3 : ℝ) / 2)) ≤
              2 * C * (R : ℝ) ^ ((5 : ℝ) / 2) *
                ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC, hweighted⟩ :=
    exists_pos_shiftedSquareAuxiliaryKey_weightedSums_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro theta Y h v D N hi
  simpa only [main3LargeAnalytic_blockAuxiliaryKeyGate] using
    hweighted (main3LargeAnalytic_auxiliaryC₀Ceiling h v)
      (main3LargeAnalytic_one_le_auxiliaryC₀Ceiling hi)

/-! ## Direct `A_a = 2|a|` forms -/

/-- Direct shift-weight form of the unweighted key sum. -/
theorem exists_pos_sum_one_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        (∑ _key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            (1 : ℝ)) ≤
          C₀ * (2 * |(shiftedSquareA h v : ℝ)|) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨C, hC, hweighted⟩ :=
    exists_pos_main3LargeAnalytic_blockAuxiliaryKeyGate_weightedSums_le_rpow ε hε
  refine ⟨2 * C * 33 * 2178 ^ ε, by positivity, ?_⟩
  intro theta Y h v D N hi
  let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hraw := (hweighted theta Y h v D N hi).1
  have htransfer := main3LargeAnalytic_auxiliaryPowerBudget_le_shiftWeight
    (q := (1 : ℝ)) (ε := ε) hi (by norm_num) hε.le
  have htransfer' : (R : ℝ) * Z ^ ε ≤
      33 * 2178 ^ ε * A ^ ((1 : ℝ) / 2 + ε) := by
    simpa only [R, Z, A, Real.rpow_one] using htransfer
  calc
    (∑ _key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (1 : ℝ)) ≤ 2 * C * (R : ℝ) * Z ^ ε := by
      simpa only [R, Z] using hraw
    _ = 2 * C * ((R : ℝ) * Z ^ ε) := by ring
    _ ≤ 2 * C *
        (33 * 2178 ^ ε * A ^ ((1 : ℝ) / 2 + ε)) :=
      mul_le_mul_of_nonneg_left htransfer' (by positivity)
    _ = (2 * C * 33 * 2178 ^ ε) *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ ((1 : ℝ) / 2 + ε) := by
      dsimp only [A]
      ring

/-- Direct shift-weight form of the linear `C₀/ell` sum. -/
theorem exists_pos_sum_ratio_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            (key.C₀ : ℝ) / (key.ell : ℝ)) ≤
          C₁ * (2 * |(shiftedSquareA h v : ℝ)|) ^ (1 + ε) := by
  obtain ⟨C, hC, hweighted⟩ :=
    exists_pos_main3LargeAnalytic_blockAuxiliaryKeyGate_weightedSums_le_rpow ε hε
  refine ⟨2 * C * 33 ^ 2 * 2178 ^ ε, by positivity, ?_⟩
  intro theta Y h v D N hi
  let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hraw := (hweighted theta Y h v D N hi).2.1
  have htransfer := main3LargeAnalytic_auxiliaryPowerBudget_le_shiftWeight
    (q := (2 : ℝ)) (ε := ε) hi (by norm_num) hε.le
  have htransfer' : (R : ℝ) ^ 2 * Z ^ ε ≤
      33 ^ 2 * 2178 ^ ε * A ^ (1 + ε) := by
    have hexponent : (2 : ℝ) / 2 + ε = 1 + ε := by ring
    simpa only [R, Z, A, Real.rpow_two, hexponent] using htransfer
  calc
    (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (key.C₀ : ℝ) / (key.ell : ℝ)) ≤
        2 * C * (R : ℝ) ^ 2 * Z ^ ε := by
      simpa only [R, Z] using hraw
    _ = 2 * C * ((R : ℝ) ^ 2 * Z ^ ε) := by ring
    _ ≤ 2 * C *
        (33 ^ 2 * 2178 ^ ε * A ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left htransfer' (by positivity)
    _ = (2 * C * 33 ^ 2 * 2178 ^ ε) *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ (1 + ε) := by
      dsimp only [A]
      ring

/-- Direct shift-weight form of the `3/2` moment.  Before the arbitrarily
small subpower loss, its exponent is `5/4`; the two field-discriminant factors
therefore leave exactly `7/8` and `9/8`. -/
theorem exists_pos_sum_ratio_threeHalves_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ ((3 : ℝ) / 2)) ≤
          C₃ * (2 * |(shiftedSquareA h v : ℝ)|) ^ ((5 : ℝ) / 4 + ε) := by
  obtain ⟨C, hC, hweighted⟩ :=
    exists_pos_main3LargeAnalytic_blockAuxiliaryKeyGate_weightedSums_le_rpow ε hε
  refine ⟨2 * C * 33 ^ ((5 : ℝ) / 2) * 2178 ^ ε, by positivity, ?_⟩
  intro theta Y h v D N hi
  let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hraw := (hweighted theta Y h v D N hi).2.2
  have htransfer := main3LargeAnalytic_auxiliaryPowerBudget_le_shiftWeight
    (q := ((5 : ℝ) / 2)) (ε := ε) hi (by norm_num) hε.le
  have htransfer' : (R : ℝ) ^ ((5 : ℝ) / 2) * Z ^ ε ≤
      33 ^ ((5 : ℝ) / 2) * 2178 ^ ε *
        A ^ ((5 : ℝ) / 4 + ε) := by
    have hexponent : (5 : ℝ) / 2 / 2 + ε = 5 / 4 + ε := by ring
    simpa only [R, Z, A, hexponent] using htransfer
  calc
    (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ ((3 : ℝ) / 2)) ≤
        2 * C * (R : ℝ) ^ ((5 : ℝ) / 2) * Z ^ ε := by
      simpa only [R, Z] using hraw
    _ = 2 * C * ((R : ℝ) ^ ((5 : ℝ) / 2) * Z ^ ε) := by ring
    _ ≤ 2 * C *
        (33 ^ ((5 : ℝ) / 2) * 2178 ^ ε *
          A ^ ((5 : ℝ) / 4 + ε)) :=
      mul_le_mul_of_nonneg_left htransfer' (by positivity)
    _ = (2 * C * 33 ^ ((5 : ℝ) / 2) * 2178 ^ ε) *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ ((5 : ℝ) / 4 + ε) := by
      dsimp only [A]
      ring

/-! The current aggregated sieve envelope also contains a quadratic ratio
weight and the divisor weight of the surface level.  The following two
corollaries are included here so the outer proof can consume this module
without reopening the scalar gate. -/

/-- Crude quadratic-ratio sum.  At `ε = 1/8` this is `A_a^(13/8)`, and
division by the square root of the field discriminant leaves `A_a^(9/8)`. -/
theorem exists_pos_sum_ratio_sq_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ 2) ≤
          C₂ * (2 * |(shiftedSquareA h v : ℝ)|) ^ ((3 : ℝ) / 2 + ε) := by
  obtain ⟨C, hC, hcard⟩ :=
    exists_pos_card_shiftedSquareAuxiliaryKeys_le_rpow ε hε
  refine ⟨2 * C * 33 ^ (3 : ℝ) * 2178 ^ ε, by positivity, ?_⟩
  intro theta Y h v D N hi
  let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hR : 1 ≤ R := main3LargeAnalytic_one_le_auxiliaryC₀Ceiling hi
  have hcard' :
      ((main3LargeAnalytic_blockAuxiliaryKeyGate h v).card : ℝ) ≤
        2 * C * (R : ℝ) * Z ^ ε := by
    simpa only [main3LargeAnalytic_blockAuxiliaryKeyGate, R, Z] using
      hcard R hR
  have hpoint (key : ShiftedSquareAuxiliaryKey)
      (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
      ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by
    have hratio := shiftedSquareAuxiliaryKey_ratio_nonneg_and_le
      (by simpa only [main3LargeAnalytic_blockAuxiliaryKeyGate, R] using hkey)
    exact pow_le_pow_left₀ hratio.1 hratio.2 2
  have hsum :
      (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
          ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ 2) ≤
        ((main3LargeAnalytic_blockAuxiliaryKeyGate h v).card : ℝ) *
          (R : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
          (R : ℝ) ^ 2 :=
        Finset.sum_le_sum fun key hkey => hpoint key hkey
      _ = _ := by simp
  have hRnonneg : (0 : ℝ) ≤ R := by positivity
  have hraw :
      (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
          ((key.C₀ : ℝ) / (key.ell : ℝ)) ^ 2) ≤
        2 * C * (R : ℝ) ^ 3 * Z ^ ε := by
    calc
      _ ≤ ((main3LargeAnalytic_blockAuxiliaryKeyGate h v).card : ℝ) *
          (R : ℝ) ^ 2 := hsum
      _ ≤ (2 * C * (R : ℝ) * Z ^ ε) * (R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard' (sq_nonneg (R : ℝ))
      _ = 2 * C * (R : ℝ) ^ 3 * Z ^ ε := by ring
  have htransfer := main3LargeAnalytic_auxiliaryPowerBudget_le_shiftWeight
    (q := (3 : ℝ)) (ε := ε) hi (by norm_num) hε.le
  have htransfer' : (R : ℝ) ^ 3 * Z ^ ε ≤
      33 ^ (3 : ℝ) * 2178 ^ ε * A ^ ((3 : ℝ) / 2 + ε) := by
    have hpow : (R : ℝ) ^ 3 = (R : ℝ) ^ (3 : ℝ) :=
      (Real.rpow_natCast (R : ℝ) 3).symm
    rw [hpow]
    simpa only [R, Z, A] using htransfer
  calc
    _ ≤ 2 * C * (R : ℝ) ^ 3 * Z ^ ε := hraw
    _ = 2 * C * ((R : ℝ) ^ 3 * Z ^ ε) := by ring
    _ ≤ 2 * C *
        (33 ^ (3 : ℝ) * 2178 ^ ε * A ^ ((3 : ℝ) / 2 + ε)) :=
      mul_le_mul_of_nonneg_left htransfer' (by positivity)
    _ = (2 * C * 33 ^ (3 : ℝ) * 2178 ^ ε) *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ ((3 : ℝ) / 2 + ε) := by
      dsimp only [A]
      ring

/-- Direct shift-weight form of the surface-level divisor sum.  Choosing
`ε = 1/8` gives the `A_a^(5/8)` cost used by the base term. -/
theorem exists_pos_sum_surfaceLevelDivisors_main3LargeAnalytic_blockAuxiliaryKeyGate_le_shiftWeight_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cdiv : ℝ, 0 < Cdiv ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
        (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
          (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ)) ≤
          Cdiv * (2 * |(shiftedSquareA h v : ℝ)|) ^ ((1 : ℝ) / 2 + ε) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨C, hC, hdiv⟩ :=
    exists_pos_sum_card_divisors_shiftedSquareAuxiliaryKeySurfaceLevel_le_rpow
      (ε / 2) hhalf
  refine ⟨C * 33 * 2178 ^ ε, by positivity, ?_⟩
  intro theta Y h v D N hi
  let R := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  let A : ℝ := 2 * |(shiftedSquareA h v : ℝ)|
  have hR : 1 ≤ R := main3LargeAnalytic_one_le_auxiliaryC₀Ceiling hi
  have hraw := hdiv R hR
  have hraw' :
      (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ)) ≤
        C * (R : ℝ) * Z ^ ε := by
    have hexponent : 2 * (ε / 2) = ε := by ring
    simpa only [main3LargeAnalytic_blockAuxiliaryKeyGate, R, Z,
      hexponent] using hraw
  have htransfer := main3LargeAnalytic_auxiliaryPowerBudget_le_shiftWeight
    (q := (1 : ℝ)) (ε := ε) hi (by norm_num) hε.le
  have htransfer' : (R : ℝ) * Z ^ ε ≤
      33 * 2178 ^ ε * A ^ ((1 : ℝ) / 2 + ε) := by
    simpa only [R, Z, A, Real.rpow_one] using htransfer
  calc
    _ ≤ C * (R : ℝ) * Z ^ ε := hraw'
    _ = C * ((R : ℝ) * Z ^ ε) := by ring
    _ ≤ C * (33 * 2178 ^ ε * A ^ ((1 : ℝ) / 2 + ε)) :=
      mul_le_mul_of_nonneg_left htransfer' hC.le
    _ = (C * 33 * 2178 ^ ε) *
        (2 * |(shiftedSquareA h v : ℝ)|) ^ ((1 : ℝ) / 2 + ε) := by
      dsimp only [A]
      ring

end

end PellPaper
