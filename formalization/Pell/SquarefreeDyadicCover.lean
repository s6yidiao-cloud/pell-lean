import Pell.FixedHeight
import Pell.ExceptionalMonotonicity

/-!
# A finite dyadic cover for squarefree Pell exceptions

This file records the elementary passage from a global squarefree exceptional
set below a power-of-two cutoff to its half-open dyadic pieces.  It is purely a
finite combinatorial reduction: no estimate for the individual pieces is used.
-/

namespace PellPaper

/-- The squarefree members of the global Pell exceptional set at an integer
cutoff. -/
noncomputable def squarefreeExceptionalSet (θ : ℝ) (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (exceptionalSet θ X).filter Squarefree

/-- The cardinality of the global squarefree exceptional set. -/
noncomputable def squarefreeExceptionalCount (θ : ℝ) (X : ℕ) : ℕ :=
  (squarefreeExceptionalSet θ X).card

/-- The finite union of the squarefree exceptional dyadic blocks at scales
`2^k` for `k < K`. -/
noncomputable def squarefreeDyadicCover (θ : ℝ) (K : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range K).biUnion
      (fun k => squarefreeDyadicExceptionalSet θ (2 ^ k))

/-- Membership in the global squarefree exceptional set is its four literal
defining conditions. -/
theorem mem_squarefreeExceptionalSet {θ : ℝ} {X w : ℕ} :
    w ∈ squarefreeExceptionalSet θ X ↔
      1 ≤ w ∧ w ≤ X ∧ Squarefree w ∧ SmallFundamentalSolution θ w := by
  constructor
  · intro hw
    obtain ⟨hwexceptional, hsf⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwone, hwX, hsmall⟩ := mem_exceptionalSet.mp hwexceptional
    exact ⟨hwone, hwX, hsf, hsmall⟩
  · rintro ⟨hwone, hwX, hsf, hsmall⟩
    exact Finset.mem_filter.mpr
      ⟨mem_exceptionalSet.mpr ⟨hwone, hwX, hsmall⟩, hsf⟩

/-- At the zero cutoff there are no positive squarefree exceptional
radicands. -/
@[simp] theorem squarefreeExceptionalSet_zero (θ : ℝ) :
    squarefreeExceptionalSet θ 0 = ∅ := by
  simp [squarefreeExceptionalSet, exceptionalSet]

/-- At a zero-scale cover there are no dyadic blocks. -/
@[simp] theorem squarefreeDyadicCover_zero (θ : ℝ) :
    squarefreeDyadicCover θ 0 = ∅ := by
  simp [squarefreeDyadicCover]

/-- The squarefree exceptional set below the strict cutoff `2^K` is exactly
the union of its dyadic blocks.  Writing the closed natural cutoff as
`2^K - 1` makes the endpoint convention explicit. -/
theorem squarefreeExceptionalSet_eq_squarefreeDyadicCover (θ : ℝ) (K : ℕ) :
    squarefreeExceptionalSet θ (2 ^ K - 1) = squarefreeDyadicCover θ K := by
  classical
  ext w
  change w ∈ squarefreeExceptionalSet θ (2 ^ K - 1) ↔
    w ∈ (Finset.range K).biUnion
      (fun k => squarefreeDyadicExceptionalSet θ (2 ^ k))
  constructor
  · intro hw
    obtain ⟨hwone, hwcut, hsf, hsmall⟩ := mem_squarefreeExceptionalSet.mp hw
    have hwpos : 0 < w := lt_of_lt_of_le Nat.zero_lt_one hwone
    have hwlt : w < 2 ^ K := by omega
    let k := Nat.log 2 w
    have hk : k < K := by
      dsimp [k]
      exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hwpos) hwlt
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, ?_⟩
    refine mem_squarefreeDyadicExceptionalSet.mpr ⟨?_, ?_, hsf, hsmall⟩
    · dsimp [k]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hwpos)
    · dsimp [k]
      simpa [Nat.succ_eq_add_one, pow_succ, Nat.mul_comm] using
        (Nat.lt_pow_succ_log_self Nat.one_lt_two w)
  · intro hw
    obtain ⟨k, hk, hwblock⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨_, hwltblock, hsf, hsmall⟩ :=
      mem_squarefreeDyadicExceptionalSet.mp hwblock
    have hklt : k < K := Finset.mem_range.mp hk
    have hkone : k + 1 ≤ K := by omega
    have hpow : 2 ^ (k + 1) ≤ 2 ^ K :=
      Nat.pow_le_pow_right (by omega) hkone
    have hwlt : w < 2 ^ K := by
      have : w < 2 ^ (k + 1) := by
        simpa [pow_succ, Nat.mul_comm] using hwltblock
      exact this.trans_le hpow
    refine mem_squarefreeExceptionalSet.mpr ⟨?_, ?_, hsf, hsmall⟩
    · exact Nat.le_of_lt
        (one_lt_of_mem_squarefreeDyadicExceptionalSet hwblock)
    · omega

/-- Any smaller integer cutoff is covered by the same finite family of
dyadic blocks.  This is the subset form used when a later argument naturally
produces a cutoff strictly below a power of two. -/
theorem squarefreeExceptionalSet_subset_squarefreeDyadicCover
    {θ : ℝ} {X K : ℕ} (hX : X < 2 ^ K) :
    squarefreeExceptionalSet θ X ⊆ squarefreeDyadicCover θ K := by
  rw [← squarefreeExceptionalSet_eq_squarefreeDyadicCover θ K]
  intro w hw
  obtain ⟨hwone, hwX, hsf, hsmall⟩ := mem_squarefreeExceptionalSet.mp hw
  apply mem_squarefreeExceptionalSet.mpr
  exact ⟨hwone, hwX.trans (Nat.le_sub_one_of_lt hX), hsf, hsmall⟩

/-- The global squarefree exceptional count below `2^K` is bounded by the
sum of the counts of its finitely many dyadic blocks. -/
theorem squarefreeExceptionalCount_le_sum_squarefreeDyadicExceptionalCount
    (θ : ℝ) (K : ℕ) :
    squarefreeExceptionalCount θ (2 ^ K - 1) ≤
      ∑ k ∈ Finset.range K, squarefreeDyadicExceptionalCount θ (2 ^ k) := by
  change (squarefreeExceptionalSet θ (2 ^ K - 1)).card ≤ _
  rw [squarefreeExceptionalSet_eq_squarefreeDyadicCover]
  change ((Finset.range K).biUnion
      (fun k => squarefreeDyadicExceptionalSet θ (2 ^ k))).card ≤ _
  simpa [squarefreeDyadicExceptionalCount] using
    (Finset.card_biUnion_le :
      ((Finset.range K).biUnion
        (fun k => squarefreeDyadicExceptionalSet θ (2 ^ k))).card ≤
        ∑ k ∈ Finset.range K,
          (squarefreeDyadicExceptionalSet θ (2 ^ k)).card)

/-- The cardinality subadditivity form of the dyadic cover at an arbitrary
integer cutoff strictly below `2^K`. -/
theorem squarefreeExceptionalCount_le_sum_squarefreeDyadicExceptionalCount_of_lt_pow
    (θ : ℝ) {X K : ℕ} (hX : X < 2 ^ K) :
    squarefreeExceptionalCount θ X ≤
      ∑ k ∈ Finset.range K, squarefreeDyadicExceptionalCount θ (2 ^ k) := by
  change (squarefreeExceptionalSet θ X).card ≤ _
  calc
    (squarefreeExceptionalSet θ X).card ≤ (squarefreeDyadicCover θ K).card :=
      Finset.card_le_card (squarefreeExceptionalSet_subset_squarefreeDyadicCover hX)
    _ ≤ ∑ k ∈ Finset.range K, squarefreeDyadicExceptionalCount θ (2 ^ k) := by
      change ((Finset.range K).biUnion
        (fun k => squarefreeDyadicExceptionalSet θ (2 ^ k))).card ≤ _
      simpa [squarefreeDyadicExceptionalCount] using
        (Finset.card_biUnion_le :
          ((Finset.range K).biUnion
            (fun k => squarefreeDyadicExceptionalSet θ (2 ^ k))).card ≤
            ∑ k ∈ Finset.range K,
              (squarefreeDyadicExceptionalSet θ (2 ^ k)).card)

end PellPaper
