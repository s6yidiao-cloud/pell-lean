import Pell.IntegerSymmetricRectangle

/-!
# Enumerating symmetric integer rectangles by natural ranges

This is the exact finite-set adapter from the geometric rectangle used after
slope reduction to the shifted product of natural ranges used by the square
sieve.  It is valid without positivity assumptions on the halfwidths.
-/

namespace PellPaper

noncomputable section

/-- The coordinatewise shifted-range embedding into an integer vector. -/
def integerSymmetricRectangleRangeEmbedding (A B : ℝ) :
    ℕ × ℕ ↪ (Fin 2 → ℤ) :=
  ((Nat.castEmbedding.trans (addLeftEmbedding (-⌊A⌋))).prodMap
      (Nat.castEmbedding.trans (addLeftEmbedding (-⌊B⌋)))).trans
    (finTwoArrowEquiv ℤ).symm.toEmbedding

@[simp]
theorem integerSymmetricRectangleRangeEmbedding_apply
    (A B : ℝ) (xy : ℕ × ℕ) :
    integerSymmetricRectangleRangeEmbedding A B xy =
      ![-⌊A⌋ + (xy.1 : ℤ), -⌊B⌋ + (xy.2 : ℤ)] := by
  ext i
  fin_cases i <;> rfl

/-- The geometric rectangle is exactly the image of the shifted product of
natural ranges. -/
theorem integerSymmetricRectangle_eq_map_rangeProduct (A B : ℝ) :
    integerSymmetricRectangle A B =
      ((Finset.range (2 * ⌊A⌋ + 1).toNat).product
          (Finset.range (2 * ⌊B⌋ + 1).toNat)).map
        (integerSymmetricRectangleRangeEmbedding A B) := by
  rw [integerSymmetricRectangle,
    integerSymmetricInterval_eq_map_range,
    integerSymmetricInterval_eq_map_range]
  let eA : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding (-⌊A⌋))
  let eB : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding (-⌊B⌋))
  let rA := Finset.range (2 * ⌊A⌋ + 1).toNat
  let rB := Finset.range (2 * ⌊B⌋ + 1).toNat
  calc
    ((rA.map eA).product (rB.map eB)).map
        (finTwoArrowEquiv ℤ).symm.toEmbedding =
        ((rA.product rB).map (eA.prodMap eB)).map
          (finTwoArrowEquiv ℤ).symm.toEmbedding := by
      congr 1
      exact (Finset.prodMap_map_product eA eB rA rB).symm
    _ = (rA.product rB).map
        (integerSymmetricRectangleRangeEmbedding A B) := by
      rw [Finset.map_map]
      rfl

/-- Filtering the geometric rectangle has exactly the same cardinality as
filtering the shifted product of natural ranges. -/
theorem card_filter_integerSymmetricRectangle_eq_rangeProduct
    (A B : ℝ) (P : (Fin 2 → ℤ) → Prop) [DecidablePred P] :
    ((integerSymmetricRectangle A B).filter P).card =
      (((Finset.range (2 * ⌊A⌋ + 1).toNat).product
          (Finset.range (2 * ⌊B⌋ + 1).toNat)).filter fun xy =>
            P ![-⌊A⌋ + (xy.1 : ℤ), -⌊B⌋ + (xy.2 : ℤ)]).card := by
  rw [integerSymmetricRectangle_eq_map_rangeProduct, Finset.filter_map,
    Finset.card_map]
  congr 1

end

end PellPaper
