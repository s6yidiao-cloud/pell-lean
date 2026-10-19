import Pell.Main3LargeAnalyticBlockCoordinateInjection
import Pell.ShiftedSquareAuxiliaryKeyCount
import Mathlib.Tactic

/-!
# Auxiliary-key partition of one main3 large-analytic block

For one active large-analytic block, the deterministic fixed-basis encoding
certificate already chosen at every attached point contains a simultaneous
normalized package.  This module sends that exact package to its scalar key
`(C₀,r,ell,bζ)` and partitions both the attached block and its injective
coordinate-code image by those keys.

The common gate uses the sharp natural ceiling
`ceil (32 * sqrt |shiftedSquareA h v|)`.  Every key lies in the literal
divisor gate from `ShiftedSquareAuxiliaryKeyCountCandidate`.  The fibre cover
and cardinality sums below are exact.  No estimate for the cardinality of an
individual fibre, coordinate cell, or shifted-square block is asserted.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The sharp common natural ceiling for the Minkowski index on the block
with fixed shifted-square parameter `shiftedSquareA h v`. -/
def main3LargeAnalytic_auxiliaryC₀Ceiling (h : ℤ) (v : ℕ) : ℕ :=
  ⌈32 * Real.sqrt |(shiftedSquareA h v : ℝ)|⌉₊

/-- The literal finite divisor gate used for all deterministic packages in
one fixed large-analytic block. -/
def main3LargeAnalytic_blockAuxiliaryKeyGate (h : ℤ) (v : ℕ) :
    Finset ShiftedSquareAuxiliaryKey :=
  shiftedSquareAuxiliaryKeys (main3LargeAnalytic_auxiliaryC₀Ceiling h v)

/-- The exact scalar key carried by the deterministically chosen certificate
at an attached block point. -/
noncomputable def main3LargeAnalytic_blockAuxiliaryKey
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    ShiftedSquareAuxiliaryKey := by
  letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY hi p
  exact ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩

/-- The attached points whose chosen package has a prescribed scalar key. -/
noncomputable def main3LargeAnalytic_blockAuxiliaryPointFiber
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    Finset (Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :=
  (squarefreeShiftedSquareBlock
    (shiftedSquareA h v) D Y N).attach.filter fun p =>
      main3LargeAnalytic_blockAuxiliaryKey htheta hY hi p = key

/-- The injective coordinate codes arising from one scalar-key fibre. -/
noncomputable def main3LargeAnalytic_blockAuxiliaryCodeFiber
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) : Finset ShiftedSquareCoordinateCode :=
  (main3LargeAnalytic_blockAuxiliaryPointFiber htheta hY hi key).image
    (main3LargeAnalytic_blockCoordinateCode htheta hY hi)

/-- The natural ceiling records the exact real upper endpoint, with less than
one unit of rounding loss. -/
theorem main3LargeAnalytic_auxiliaryC₀Ceiling_spec (h : ℤ) (v : ℕ) :
    32 * Real.sqrt |(shiftedSquareA h v : ℝ)| ≤
        (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ∧
      (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) <
        32 * Real.sqrt |(shiftedSquareA h v : ℝ)| + 1 := by
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one (by positivity)

/-- An active index has a nonzero shift, so its common auxiliary ceiling is
at least one. -/
theorem main3LargeAnalytic_one_le_auxiliaryC₀Ceiling
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    1 ≤ main3LargeAnalytic_auxiliaryC₀Ceiling h v := by
  have hiActive :=
    (mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi).1
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiActive
  have hshift :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
      hiBroad hcell
  have ha0 : shiftedSquareA h v ≠ 0 := hshift.2.2.1
  rw [main3LargeAnalytic_auxiliaryC₀Ceiling, Nat.one_le_ceil_iff]
  have ha0Real : (shiftedSquareA h v : ℝ) ≠ 0 := by
    exact_mod_cast ha0
  have habsPos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr ha0Real
  positivity

/-- The `C₀` in the chosen point certificate is bounded by the common sharp
ceiling, using the real `32*sqrt |a|` bound from that same certificate. -/
theorem main3LargeAnalytic_blockCertificate_C₀_le_auxiliaryC₀Ceiling
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
      htheta hY hi p
    C.P.minkowski.C₀ ≤ main3LargeAnalytic_auxiliaryC₀Ceiling h v := by
  exact
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    by
      let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
        htheta hY hi p
      have hreal : (C.P.minkowski.C₀ : ℝ) ≤
          (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) :=
        C.scaled.C₀_le_thirtytwo_mul_sqrt_abs.trans
          (main3LargeAnalytic_auxiliaryC₀Ceiling_spec h v).1
      exact_mod_cast hreal

/-- Every attached point's deterministic scalar key belongs to the literal
divisor gate at the sharp common ceiling. -/
theorem main3LargeAnalytic_blockAuxiliaryKey_mem_gate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    main3LargeAnalytic_blockAuxiliaryKey htheta hY hi p ∈
      main3LargeAnalytic_blockAuxiliaryKeyGate h v := by
  have hFact : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY hi p
  have hC₀ : C.P.minkowski.C₀ ≤
      main3LargeAnalytic_auxiliaryC₀Ceiling h v :=
    main3LargeAnalytic_blockCertificate_C₀_le_auxiliaryC₀Ceiling
      htheta hY hi p
  simpa only [main3LargeAnalytic_blockAuxiliaryKey,
    main3LargeAnalytic_blockAuxiliaryKeyGate, C] using
      @shiftedSquareAuxiliaryKey_mem _ _ _ _ _ hFact _ C.P hC₀

@[simp]
theorem mem_main3LargeAnalytic_blockAuxiliaryPointFiber_iff
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N} :
    p ∈ main3LargeAnalytic_blockAuxiliaryPointFiber htheta hY hi key ↔
      main3LargeAnalytic_blockAuxiliaryKey htheta hY hi p = key := by
  simp [main3LargeAnalytic_blockAuxiliaryPointFiber]

/-- Distinct scalar keys give disjoint attached-point fibres. -/
theorem main3LargeAnalytic_blockAuxiliaryPointFiber_disjoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key₁ key₂ : ShiftedSquareAuxiliaryKey} (hne : key₁ ≠ key₂) :
    Disjoint
      (main3LargeAnalytic_blockAuxiliaryPointFiber htheta hY hi key₁)
      (main3LargeAnalytic_blockAuxiliaryPointFiber htheta hY hi key₂) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp₁ hp₂
  apply hne
  exact
    (mem_main3LargeAnalytic_blockAuxiliaryPointFiber_iff
      htheta hY hi).mp hp₁ |>.symm.trans
        ((mem_main3LargeAnalytic_blockAuxiliaryPointFiber_iff
          htheta hY hi).mp hp₂)

/-- The literal union of all admissible point fibres is exactly the attached
large-analytic block. -/
theorem main3LargeAnalytic_blockAuxiliaryPointFibers_cover
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).attach =
      (main3LargeAnalytic_blockAuxiliaryKeyGate h v).biUnion fun key =>
        main3LargeAnalytic_blockAuxiliaryPointFiber htheta hY hi key := by
  classical
  ext p
  constructor
  · intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨main3LargeAnalytic_blockAuxiliaryKey htheta hY hi p,
      main3LargeAnalytic_blockAuxiliaryKey_mem_gate htheta hY hi p, ?_⟩
    exact (mem_main3LargeAnalytic_blockAuxiliaryPointFiber_iff
      htheta hY hi).mpr rfl
  · intro hp
    obtain ⟨key, _hkey, hpFiber⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpFiber).1

/-- Injectivity of the complete coordinate code preserves the cardinality of
each individual scalar-key fibre exactly. -/
theorem card_main3LargeAnalytic_blockAuxiliaryCodeFiber_eq_pointFiber
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    (main3LargeAnalytic_blockAuxiliaryCodeFiber
        htheta hY hi key).card =
      (main3LargeAnalytic_blockAuxiliaryPointFiber
        htheta hY hi key).card := by
  classical
  exact Finset.card_image_of_injective _
    (main3LargeAnalytic_blockCoordinateCode_injective htheta hY hi)

/-- The complete coordinate-code image is exactly covered by the code fibres
over the literal admissible key gate. -/
theorem main3LargeAnalytic_blockAuxiliaryCodeFibers_cover
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    main3LargeAnalytic_blockCoordinateCodeImage htheta hY hi =
      (main3LargeAnalytic_blockAuxiliaryKeyGate h v).biUnion fun key =>
        main3LargeAnalytic_blockAuxiliaryCodeFiber htheta hY hi key := by
  classical
  ext code
  constructor
  · intro hcode
    obtain ⟨p, hp, hpCode⟩ := Finset.mem_image.mp hcode
    apply Finset.mem_biUnion.mpr
    refine ⟨main3LargeAnalytic_blockAuxiliaryKey htheta hY hi p,
      main3LargeAnalytic_blockAuxiliaryKey_mem_gate htheta hY hi p, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p, ?_, hpCode⟩
    exact (mem_main3LargeAnalytic_blockAuxiliaryPointFiber_iff
      htheta hY hi).mpr rfl
  · intro hcode
    obtain ⟨key, _hkey, hcodeFiber⟩ := Finset.mem_biUnion.mp hcode
    obtain ⟨p, hpFiber, hpCode⟩ := Finset.mem_image.mp hcodeFiber
    apply Finset.mem_image.mpr
    refine ⟨p, (Finset.mem_filter.mp hpFiber).1, hpCode⟩

/-- The block cardinality is the exact sum of its attached point-fibre
cardinalities over the literal divisor gate. -/
theorem card_main3LargeAnalytic_block_eq_sum_auxiliaryPointFibers
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card =
      ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (main3LargeAnalytic_blockAuxiliaryPointFiber
          htheta hY hi key).card := by
  classical
  have hmap :
      ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).attach :
        Set (Main3LargeAnalyticSquarefreeBlockPoint h v D Y N)).MapsTo
          (main3LargeAnalytic_blockAuxiliaryKey htheta hY hi)
          (main3LargeAnalytic_blockAuxiliaryKeyGate h v) := by
    intro p _hp
    exact main3LargeAnalytic_blockAuxiliaryKey_mem_gate htheta hY hi p
  rw [← Finset.card_attach]
  simpa only [main3LargeAnalytic_blockAuxiliaryPointFiber] using
    Finset.card_eq_sum_card_fiberwise hmap

/-- Equivalently, the original block cardinality is the exact sum of the
injective coordinate-code fibre cardinalities. -/
theorem card_main3LargeAnalytic_block_eq_sum_auxiliaryCodeFibers
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card =
      ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (main3LargeAnalytic_blockAuxiliaryCodeFiber
          htheta hY hi key).card := by
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryPointFibers
    htheta hY hi]
  apply Finset.sum_congr rfl
  intro key _hkey
  rw [card_main3LargeAnalytic_blockAuxiliaryCodeFiber_eq_pointFiber]

/-- The same exact sum is the cardinality of the complete block code image. -/
theorem card_main3LargeAnalytic_blockCoordinateCodeImage_eq_sum_auxiliaryCodeFibers
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (main3LargeAnalytic_blockCoordinateCodeImage htheta hY hi).card =
      ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        (main3LargeAnalytic_blockAuxiliaryCodeFiber
          htheta hY hi key).card := by
  rw [card_main3LargeAnalytic_blockCoordinateCodeImage_eq]
  exact card_main3LargeAnalytic_block_eq_sum_auxiliaryCodeFibers
    htheta hY hi

/-- Uniform subpower control of the number of possible scalar keys.  The
constant is chosen after `ε` and before all block and growing-`theta`
parameters. -/
theorem exists_pos_uniform_card_main3LargeAnalytic_blockAuxiliaryKeyGate_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (theta : ℝ) (Y : ℕ) (h : ℤ) (v D N : ℕ),
        (h, v, D, N) ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y →
          ((main3LargeAnalytic_blockAuxiliaryKeyGate h v).card : ℝ) ≤
            2 * C * (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) *
              (((2 * (main3LargeAnalytic_auxiliaryC₀Ceiling h v) ^ 2 : ℕ) : ℝ) ^ ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_card_shiftedSquareAuxiliaryKeys_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro theta Y h v D N hi
  exact hbound (main3LargeAnalytic_auxiliaryC₀Ceiling h v)
    (main3LargeAnalytic_one_le_auxiliaryC₀Ceiling hi)

end

end PellPaper
