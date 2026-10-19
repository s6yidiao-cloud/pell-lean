import Pell.DyadicSquarePartReduction
import Pell.ExceptionalMonotonicity
import Pell.IntegerToRealPell
import Pell.SquarefreeGlobalReduction

/-!
# From arbitrary dyadic Pell blocks to the global power-saving statement

The fixed-height proposition controls only squarefree blocks.  To reach the
actual `PellPowerSaving` target one additionally needs a square-part lifting
estimate for the *arbitrary* dyadic family below.  This file makes that final
logical handoff explicit: it proves the dyadic cover, finite geometric sum,
and real-cutoff passage, while leaving the new dyadic estimate as a stated
proposition rather than an axiom.
-/

open Filter
open scoped BigOperators

namespace PellPaper

/-- The remaining all-radicand dyadic estimate needed for the Pell theorem.

Unlike `FixedHeightSquarefree`, this count includes arbitrary square parts.
It is therefore exactly the output required from the missing square-part
lifting/determinant argument, at the exponent of `PellPowerSaving`. -/
def DyadicSquarePartPowerSaving : Prop :=
  ∀ θ : ℝ, 3 ≤ θ → ∀ ε : ℝ, 0 < ε →
    Asymptotics.IsBigO atTop
      (fun Y : ℕ => (dyadicSquarePartExceptionalCount θ Y : ℝ))
      (fun Y : ℕ => (Y : ℝ) ^ (1 - Delta θ + ε))

/-- The arbitrary dyadic exceptional family is contained in its ambient
interval, giving the elementary scale bound used to absorb finitely many
pre-asymptotic dyadic scales. -/
theorem dyadicSquarePartExceptionalCount_le_scale (θ : ℝ) (Y : ℕ) :
    dyadicSquarePartExceptionalCount θ Y ≤ Y := by
  classical
  have hcard : (dyadicSquarePartExceptionalSet θ Y).card ≤
      (Finset.Ico Y (2 * Y)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [dyadicSquarePartExceptionalCount, dyadicSquarePartExceptionalSet,
    Nat.card_Ico, two_mul] using hcard

/-- The finite union of arbitrary dyadic exceptional blocks below `2^K`. -/
noncomputable def dyadicSquarePartCover (θ : ℝ) (K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range K).biUnion
    (fun k => dyadicSquarePartExceptionalSet θ (2 ^ k))

/-- The global exceptional set below the strict cutoff `2^K` is exactly its
finite union of arbitrary dyadic blocks. -/
theorem exceptionalSet_eq_dyadicSquarePartCover (θ : ℝ) (K : ℕ) :
    exceptionalSet θ (2 ^ K - 1) = dyadicSquarePartCover θ K := by
  classical
  ext m
  change m ∈ exceptionalSet θ (2 ^ K - 1) ↔
    m ∈ (Finset.range K).biUnion
      (fun k => dyadicSquarePartExceptionalSet θ (2 ^ k))
  constructor
  · intro hm
    obtain ⟨hmone, hmcut, hsmall⟩ := mem_exceptionalSet.mp hm
    have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmone
    have hmlt : m < 2 ^ K := by omega
    let k := Nat.log 2 m
    have hk : k < K := by
      dsimp [k]
      exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hmpos) hmlt
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, ?_⟩
    refine mem_dyadicSquarePartExceptionalSet.mpr ⟨?_, ?_, hsmall⟩
    · dsimp [k]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hmpos)
    · dsimp [k]
      simpa [Nat.succ_eq_add_one, pow_succ, Nat.mul_comm] using
        (Nat.lt_pow_succ_log_self Nat.one_lt_two m)
  · intro hm
    obtain ⟨k, hk, hmblock⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨_, hmltblock, hsmall⟩ :=
      mem_dyadicSquarePartExceptionalSet.mp hmblock
    have hklt : k < K := Finset.mem_range.mp hk
    have hkone : k + 1 ≤ K := by omega
    have hpow : 2 ^ (k + 1) ≤ 2 ^ K :=
      Nat.pow_le_pow_right (by omega) hkone
    have hmlt : m < 2 ^ K := by
      have : m < 2 ^ (k + 1) := by
        simpa [pow_succ, Nat.mul_comm] using hmltblock
      exact this.trans_le hpow
    refine mem_exceptionalSet.mpr ⟨?_, ?_, hsmall⟩
    · exact Nat.succ_le_iff.mpr
        (positive_nonsquare_of_smallFundamentalSolution hsmall).1
    · omega

/-- Cardinality subadditivity for the arbitrary dyadic cover. -/
theorem EInt_le_sum_dyadicSquarePartExceptionalCount
    (θ : ℝ) (K : ℕ) :
    EInt θ (2 ^ K - 1) ≤
      ∑ k ∈ Finset.range K, dyadicSquarePartExceptionalCount θ (2 ^ k) := by
  change (exceptionalSet θ (2 ^ K - 1)).card ≤ _
  rw [exceptionalSet_eq_dyadicSquarePartCover]
  change ((Finset.range K).biUnion
      (fun k => dyadicSquarePartExceptionalSet θ (2 ^ k))).card ≤ _
  simpa [dyadicSquarePartExceptionalCount] using
    (Finset.card_biUnion_le :
      ((Finset.range K).biUnion
        (fun k => dyadicSquarePartExceptionalSet θ (2 ^ k))).card ≤
        ∑ k ∈ Finset.range K,
          (dyadicSquarePartExceptionalSet θ (2 ^ k)).card)

/-- An eventual all-scale dyadic estimate can be made uniform on the
power-of-two scales.  The finite initial segment is absorbed using the
elementary interval-length bound above. -/
theorem exists_all_pow_two_dyadicSquarePart_bound
    {θ p : ℝ} (hp : 0 < p)
    (hbound : Asymptotics.IsBigO atTop
      (fun Y : ℕ => (dyadicSquarePartExceptionalCount θ Y : ℝ))
      (fun Y : ℕ => (Y : ℝ) ^ p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ p := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hbound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  let C : ℝ := max c ((2 ^ N : ℕ) : ℝ)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact (Nat.cast_nonneg _).trans (le_max_right _ _)
  · intro k
    have hscale_nonneg : 0 ≤ ((2 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpow_nonneg : 0 ≤ ((2 ^ k : ℕ) : ℝ) ^ p :=
      Real.rpow_nonneg hscale_nonneg _
    by_cases hk : k < N
    · have hpow_nat : 2 ^ k ≤ 2 ^ N :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hk)
      have hscale_le_C : ((2 ^ k : ℕ) : ℝ) ≤ C := by
        calc
          ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by
            exact_mod_cast hpow_nat
          _ ≤ C := by
            dsimp [C]
            exact le_max_right _ _
      have hcount_le_scale :
          (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) ≤
            ((2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast dyadicSquarePartExceptionalCount_le_scale θ (2 ^ k)
      have hC_nonneg : 0 ≤ C := by
        dsimp [C]
        exact (Nat.cast_nonneg _).trans (le_max_right _ _)
      have hpow_one : 1 ≤ ((2 ^ k : ℕ) : ℝ) ^ p := by
        apply Real.one_le_rpow
        · exact_mod_cast Nat.one_le_two_pow
        · exact hp.le
      exact hcount_le_scale.trans
        (hscale_le_C.trans (le_mul_of_one_le_right hC_nonneg hpow_one))
    · have hNk : N ≤ k := Nat.le_of_not_gt hk
      have hNscale : N ≤ 2 ^ k := by
        exact hNk.trans (Nat.le_of_lt Nat.lt_two_pow_self)
      have hbound' := hN (2 ^ k) hNscale
      have hcount_nonneg :
          0 ≤ (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) :=
        Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hcount_nonneg,
        Real.norm_eq_abs, abs_of_nonneg hpow_nonneg] at hbound'
      calc
        (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) ≤
            c * ((2 ^ k : ℕ) : ℝ) ^ p := hbound'
        _ ≤ C * ((2 ^ k : ℕ) : ℝ) ^ p := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [C]
            exact le_max_left _ _
          · exact hpow_nonneg

/-- A uniform power bound on arbitrary dyadic blocks gives the corresponding
global bound at every power-of-two cutoff. -/
theorem EInt_le_geometric_of_dyadicSquarePart_bound
    {θ C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hdyadic : ∀ k : ℕ,
      (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ p)
    (K : ℕ) :
    (EInt θ (2 ^ K - 1) : ℝ) ≤
      C * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by
  have hcover := EInt_le_sum_dyadicSquarePartExceptionalCount θ K
  have hcoverR : (EInt θ (2 ^ K - 1) : ℝ) ≤
      ∑ k ∈ Finset.range K,
        (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) := by
    exact_mod_cast hcover
  calc
    (EInt θ (2 ^ K - 1) : ℝ) ≤
        ∑ k ∈ Finset.range K,
          (dyadicSquarePartExceptionalCount θ (2 ^ k) : ℝ) := hcoverR
    _ ≤ ∑ k ∈ Finset.range K, C * ((2 ^ k : ℕ) : ℝ) ^ p := by
      exact Finset.sum_le_sum fun k hk => hdyadic k
    _ = C * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
      rw [Finset.mul_sum]
    _ ≤ C * (((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) := by
      exact mul_le_mul_of_nonneg_left (sum_cast_two_pow_rpow_le p hp K) hC
    _ = C * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by ring

/-- The next dyadic scale above a positive integer is at most twice that
integer.  This is the elementary rounding loss needed to turn a bound at
power-of-two cutoffs into one at arbitrary cutoffs. -/
theorem two_pow_log_add_one_le_two_mul {N : ℕ} (hN : 1 ≤ N) :
    2 ^ (Nat.log 2 N + 1) ≤ 2 * N := by
  have hNpos : 0 < N := by omega
  have hlog : 2 ^ Nat.log 2 N ≤ N :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hNpos)
  calc
    2 ^ (Nat.log 2 N + 1) = 2 ^ Nat.log 2 N * 2 := by
      rw [pow_succ]
    _ ≤ N * 2 := Nat.mul_le_mul_right 2 hlog
    _ = 2 * N := by omega

/-- A dyadic all-scale big-O estimate gives an eventual integer-cutoff power
bound for the full Pell exceptional count.  The loss from rounding the cutoff
to its next dyadic scale is made explicit in the resulting constant. -/
theorem exists_eventual_integer_bound_of_dyadicSquarePart_estimate
    {θ p : ℝ} (hp : 0 < p)
    (hbound : Asymptotics.IsBigO atTop
      (fun Y : ℕ => (dyadicSquarePartExceptionalCount θ Y : ℝ))
      (fun Y : ℕ => (Y : ℝ) ^ p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (EInt θ N : ℝ) ≤ C * (N : ℝ) ^ p := by
  obtain ⟨C₀, hC₀, hblocks⟩ :=
    exists_all_pow_two_dyadicSquarePart_bound hp hbound
  have hr : 1 < (2 : ℝ) ^ p :=
    Real.one_lt_rpow (by norm_num) hp
  have hden : 0 < (2 : ℝ) ^ p - 1 := sub_pos.mpr hr
  let C : ℝ := C₀ * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1)
  refine ⟨C, ?_, 1, ?_⟩
  · dsimp [C]
    exact div_nonneg
      (mul_nonneg hC₀ (Real.rpow_nonneg (by positivity) _)) hden.le
  · intro N hN
    let K : ℕ := Nat.log 2 N + 1
    have hNlt : N < 2 ^ K := by
      dsimp [K]
      simpa [Nat.succ_eq_add_one] using
        (Nat.lt_pow_succ_log_self Nat.one_lt_two N)
    have hcutoff : N ≤ 2 ^ K - 1 := Nat.le_sub_one_of_lt hNlt
    have hmono : (EInt θ N : ℝ) ≤ (EInt θ (2 ^ K - 1) : ℝ) := by
      exact_mod_cast EInt_le_of_cutoff_le θ hcutoff
    have hglobal := EInt_le_geometric_of_dyadicSquarePart_bound
      hC₀ hp hblocks K
    have hnext : 2 ^ K ≤ 2 * N := by
      dsimp [K]
      exact two_pow_log_add_one_le_two_mul hN
    have hnextR : ((2 ^ K : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast hnext
    have hpow : ((2 ^ K : ℕ) : ℝ) ^ p ≤ ((2 * N : ℕ) : ℝ) ^ p :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hnextR hp.le
    have htwo : ((2 * N : ℕ) : ℝ) ^ p =
        (2 : ℝ) ^ p * (N : ℝ) ^ p := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
    have hscaled :
        C₀ * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤
          C₀ * ((2 * N : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hpow hC₀
      · exact hden.le
    calc
      (EInt θ N : ℝ) ≤ C₀ * ((2 ^ K : ℕ) : ℝ) ^ p /
          ((2 : ℝ) ^ p - 1) := hmono.trans hglobal
      _ ≤ C₀ * ((2 * N : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := hscaled
      _ = C * (N : ℝ) ^ p := by
        rw [htwo]
        dsimp [C]
        ring

/-- The explicit arbitrary-dyadic estimate above supplies the exact
`PellPowerSaving` proposition from `Definitions.lean`.  This theorem does not
prove that estimate: the determinant/square-part lifting argument is precisely
what remains to establish `DyadicSquarePartPowerSaving`. -/
theorem pellPowerSaving_of_dyadicSquarePartPowerSaving
    (hdyadic : DyadicSquarePartPowerSaving) :
    PellPowerSaving := by
  apply pellPowerSaving_of_eventual_integer_estimates
  intro θ hθ ε hε
  have hp : 0 < 1 - Delta θ + ε := by
    have hhalf := Delta_le_one_half θ
    linarith
  exact exists_eventual_integer_bound_of_dyadicSquarePart_estimate hp
    (hdyadic θ hθ ε hε)

end PellPaper
