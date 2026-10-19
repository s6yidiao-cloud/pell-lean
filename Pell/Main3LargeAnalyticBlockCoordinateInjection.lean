import Pell.Main3LargeAnalyticFixedBasisEncoding
import Mathlib.Tactic

/-!
# Injective coordinate codes for one main3 large-analytic block

For a fixed active large-analytic index, this module chooses one fixed-basis
encoding certificate deterministically for every point of the corresponding
squarefree shifted-square block.  The resulting complete coordinate code is
injective: equality of codes first gives equality of the fixed-basis encoded
solutions, whose retained original triples are exactly the subtype values.

The image of the attached block under this code therefore has exactly the
cardinality of the original block.  This is a point/block-level encoding
statement only; no coordinate container, box estimate, cell count, or
asymptotic bound is asserted.
-/

namespace PellPaper

noncomputable section

/-- Points of one fixed squarefree shifted-square block, retained with their
literal block-membership proofs. -/
abbrev Main3LargeAnalyticSquarefreeBlockPoint
    (h : ℤ) (v D Y N : ℕ) :=
  {p : ℕ × ℕ × ℕ //
    p ∈ squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N}

/-- Deterministically choose one fixed-basis encoding certificate for every
point of a fixed active large-analytic block.  The only nonconstructive step
is `Classical.choice` applied to the predecessor's pointwise `Nonempty`
certificate. -/
noncomputable def main3LargeAnalytic_blockFixedBasisEncodingCertificate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    let heq := main3LargeAnalytic_squarefreeBlock_equation p.2
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let B := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    Main3LargeAnalyticFixedBasisEncodingCertificate
      (D := D) (Y := Y) (N := N) B heq := by
  exact Classical.choice
    (nonempty_main3LargeAnalytic_fixedBasisEncodingCertificate
      htheta hY hi p.2)

/-- The complete coordinate code of the deterministically chosen certificate
at a block point.  Its codomain is independent of the point. -/
noncomputable def main3LargeAnalytic_blockCoordinateCode
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    ShiftedSquareCoordinateCode := by
  letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  exact (main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY hi p).encoded.code

/-- The encoded solution chosen at `p` retains exactly the value of the
original attached block point. -/
theorem main3LargeAnalytic_blockEncoding_originalPoint
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
    (C.encoded.solution.d, C.encoded.solution.w,
      C.encoded.solution.n) = p.1 := by
  exact
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    by
      rcases p with ⟨⟨d, w, n⟩, hp⟩
      exact
        (main3LargeAnalytic_blockFixedBasisEncodingCertificate
          htheta hY hi ⟨(d, w, n), hp⟩).encoded_originalTriple

/-- The deterministically chosen complete coordinate code is injective on
the attached points of one fixed block. -/
theorem main3LargeAnalytic_blockCoordinateCode_injective
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Function.Injective
      (main3LargeAnalytic_blockCoordinateCode htheta hY hi) := by
  exact
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    by
      intro p q hcode
      let Cp := main3LargeAnalytic_blockFixedBasisEncodingCertificate
        htheta hY hi p
      let Cq := main3LargeAnalytic_blockFixedBasisEncodingCertificate
        htheta hY hi q
      have hencoded : Cp.encoded = Cq.encoded :=
        ShiftedSquareEncodedFixedBasisSolution.code_injective hcode
      have hp := main3LargeAnalytic_blockEncoding_originalPoint
        htheta hY hi p
      have hq := main3LargeAnalytic_blockEncoding_originalPoint
        htheta hY hi q
      apply Subtype.ext
      calc
        p.1 = (Cp.encoded.solution.d, Cp.encoded.solution.w,
            Cp.encoded.solution.n) := hp.symm
        _ = (Cq.encoded.solution.d, Cq.encoded.solution.w,
            Cq.encoded.solution.n) := by rw [hencoded]
        _ = q.1 := hq

/-- The finite image of one fixed large-analytic squarefree block under its
deterministically chosen complete coordinate code. -/
noncomputable def main3LargeAnalytic_blockCoordinateCodeImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Finset ShiftedSquareCoordinateCode :=
  (squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N).attach.image
    (main3LargeAnalytic_blockCoordinateCode htheta hY hi)

/-- Passing from the block to the complete coordinate-code image preserves
cardinality exactly. -/
theorem card_main3LargeAnalytic_blockCoordinateCodeImage_eq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (main3LargeAnalytic_blockCoordinateCodeImage htheta hY hi).card =
      (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card := by
  classical
  rw [main3LargeAnalytic_blockCoordinateCodeImage,
    Finset.card_image_of_injective _
      (main3LargeAnalytic_blockCoordinateCode_injective htheta hY hi),
    Finset.card_attach]

end

end PellPaper
