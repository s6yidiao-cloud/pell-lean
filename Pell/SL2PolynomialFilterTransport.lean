import Pell.SL2FinitePrimitiveTransport
import Pell.BinaryLinearSubstitutionSL2

/-!
# Exact polynomial-filter transport through integral `SL₂` coordinates

The reduced target set is represented in inverse coordinates by
`sl2InverseTargetImage W T`.  With the row convention for polynomial
substitution, filtering those inverse coordinates by `K(W*x)` is exactly the
inverse image of filtering the original targets by `K`.  This is an equality
of finite sets and hence preserves filtered cardinality; it does not replace a
source-tuple family by its target image.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- Exact transport of an arbitrary predicate on polynomial values through
the same integral determinant-one coordinate change. -/
theorem filter_sl2InverseTargetImage_binaryLinearSubstitution
    (W : SL(2, ℤ)) (T : Finset (Fin 2 → ℤ))
    (K : MvPolynomial (Fin 2) ℤ) (P : ℤ → Prop) [DecidablePred P] :
    (sl2InverseTargetImage W T).filter (fun x =>
        P (MvPolynomial.eval x
          (binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K))) =
      sl2InverseTargetImage W
        (T.filter (fun y => P (MvPolynomial.eval y K))) := by
  ext x
  simp only [Finset.mem_filter, mem_sl2InverseTargetImage_iff,
    eval_binaryLinearSubstitution]
  rfl

/-- Consequently, every value-defined target filter has exactly the same
cardinality in the inverse coordinates. -/
theorem card_filter_sl2InverseTargetImage_binaryLinearSubstitution
    (W : SL(2, ℤ)) (T : Finset (Fin 2 → ℤ))
    (K : MvPolynomial (Fin 2) ℤ) (P : ℤ → Prop) [DecidablePred P] :
    (((sl2InverseTargetImage W T).filter (fun x =>
        P (MvPolynomial.eval x
          (binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) K)))).card) =
      ((T.filter (fun y => P (MvPolynomial.eval y K))).card) := by
  rw [filter_sl2InverseTargetImage_binaryLinearSubstitution,
    card_sl2InverseTargetImage]

end
end PellPaper
