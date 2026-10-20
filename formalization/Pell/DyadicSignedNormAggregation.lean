import Pell.FixedNormDyadicFibreCount

/-!
# Aggregating the four literal signed norm levels

A finite family whose actual integer values lie in `{1,-1,2,-2}` has at
most four times a common nonnegative fibre capacity. Applied to the literal
dyadic norm `v*e^2-u*d^2`, this counts all permitted levels at fixed raw
`u,v` in one box, with bound `96*Q`. No target-slope or global aggregation
is asserted.
-/

namespace PellPaper

open scoped BigOperators

/-- The actual image of a signed integer-valued finite family has at most
four elements. Summing its disjoint level fibres gives four times any
common nonnegative real capacity. -/
theorem card_le_four_mul_of_signed_integer_fibres
    {α : Type*} (S : Finset α) (f : α → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hsigned : ∀ z ∈ S, IsSignedDyadicDifference (f z))
    (hfibre : ∀ h : ℤ, IsSignedDyadicDifference h →
      ((S.filter fun z => f z = h).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ 4 * B := by
  classical
  have himage : S.image f ⊆ ({1, -1, 2, -2} : Finset ℤ) := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    simpa only [Finset.mem_insert, Finset.mem_singleton, IsSignedDyadicDifference]
      using hsigned z hz
  have hcard : (S.image f).card ≤ 4 := by
    calc
      (S.image f).card ≤ ({1, -1, 2, -2} : Finset ℤ).card :=
        Finset.card_le_card himage
      _ = 4 := by decide
  calc
    (S.card : ℝ) = ∑ h ∈ S.image f, ((S.filter fun z => f z = h).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _ ∈ S.image f, B := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
      exact hfibre (f z) (hsigned z hz)
    _ = ((S.image f).card : ℝ) * B := by simp
    _ ≤ 4 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- All four signed norm levels of an actual finite natural-pair family
in one dyadic box at fixed raw `u,v` have total cardinality at most `96*Q`.
The actual norm and its signedness come from the factor condition; no
single fixed level or norm equation is supplied by the caller. -/
theorem card_dyadic_fixedParameter_pairs_le_ninetySix_mul_Q
    (θ Q : ℝ) (Y u v : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (S : Finset (ℕ × ℕ))
    (hcond : ∀ z ∈ S, DyadicFactorCondition θ Y z.1 z.2 u v)
    (hbox : ∀ z ∈ S, (z.1, z.2, u, v) ∈ dyadicBox i) :
    (S.card : ℝ) ≤ 96 * Q := by
  let f : (ℕ × ℕ) → ℤ := fun z =>
    (v : ℤ) * (z.2 : ℤ) ^ 2 - (u : ℤ) * (z.1 : ℤ) ^ 2
  have hsigned : ∀ z ∈ S, IsSignedDyadicDifference (f z) := by
    intro z hz
    apply isSignedDyadicDifference_of_dyadicFactorCondition (hcond z hz)
    dsimp [f]
    ring
  have hfibre : ∀ h : ℤ, IsSignedDyadicDifference h →
      ((S.filter fun z => f z = h).card : ℝ) ≤ 24 * Q := by
    intro h _
    apply card_dyadic_fixedNorm_pairs_le_twentyFour_mul_Q θ Q Y u v h i hY hQ hxQ
    · intro z hz
      exact hcond z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact hbox z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hbound := card_le_four_mul_of_signed_integer_fibres S f (24 * Q)
    (by linarith) hsigned hfibre
  nlinarith

end PellPaper
