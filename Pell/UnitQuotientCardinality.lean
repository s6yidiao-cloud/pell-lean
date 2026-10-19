import Pell.QuadraticOrderPellFundamentalDiscriminantUnitBridge
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Fintype

/-!
# Finite reduction modulo two for quadratic rings of integers

This file isolates the finite quotient underlying the unit-index step in the
field/class-average argument.  It contains no comparison of fundamental
units; it only records the cardinality of the reduction modulo two.
-/

namespace PellPaper

/-- In any commutative ring whose quotient modulo `2` has four elements,
every unit has a positive power at most three that is congruent to one modulo
twice the ring.  This is the finite-group core of the change-of-order unit
index argument. -/
theorem exists_pow_eq_one_add_two_zsmul_of_quotient_card_eq_four
    {R : Type*} [CommRing R]
    (hcard : Nat.card
      (R ⧸ Ideal.span ({(2 : R)} : Set R)) = 4)
    (u : Rˣ) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 3 ∧ ∃ x : R,
      ((u ^ j : Rˣ) : R) = 1 + (2 : ℤ) • x := by
  let I : Ideal R := Ideal.span ({(2 : R)} : Set R)
  let Q := R ⧸ I
  have hcardQ : Nat.card Q = 4 := by
    simpa [Q, I] using hcard
  let _ : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcardQ]
    norm_num)
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ : Nontrivial Q := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Fintype.card_eq_nat_card, hcardQ]
    norm_num)
  let v : Qˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom u
  refine ⟨orderOf v, orderOf_pos v, ?_, ?_⟩
  · have hjlt : orderOf v < 4 := by
      calc
        orderOf v ≤ Nat.card Qˣ := orderOf_le_card
        _ < Nat.card Q := natCard_units_lt Q
        _ = 4 := hcardQ
    omega
  · have hpow : v ^ orderOf v = 1 := pow_orderOf_eq_one v
    have hpowval := congrArg (fun z : Qˣ => (z : Q)) hpow
    change (Ideal.Quotient.mk I (u : R)) ^ orderOf v = 1 at hpowval
    have hquot : Ideal.Quotient.mk I
        ((u ^ orderOf v : Rˣ) : R) = 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact hpowval
    have hmem : ((u ^ orderOf v : Rˣ) : R) - 1 ∈ I := by
      apply Ideal.Quotient.eq.mp
      simpa using hquot
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨x, ?_⟩
    calc
      ((u ^ orderOf v : Rˣ) : R) =
          1 + (((u ^ orderOf v : Rˣ) : R) - 1) := by ring
      _ = 1 + x * (2 : R) := by rw [← hx]
      _ = 1 + (2 : ℤ) • x := by
        simp only [two_zsmul]
        ring

theorem rationalQuadraticRingOfIntegers_modTwo_card
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Nat.card
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra d) ⧸
        Ideal.span ({(2 : NumberField.RingOfIntegers (rationalQuadraticAlgebra d))} : Set _)) =
      4 := by
  let _ : NumberField (rationalQuadraticAlgebra d) :=
    rationalQuadraticAlgebra_numberField d
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have hnorm := Ideal.absNorm_span_natCast
    (S := NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) 2
  rw [show (2 : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) =
      ((2 : ℕ) : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) by norm_num,
    hnorm, NumberField.RingOfIntegers.rank,
    QuadraticAlgebra.finrank_eq_two]
  norm_num

/-- At a positive fundamental discriminant, every maximal-order unit has a
positive exponent at most three whose doubled power belongs to the embedded
norm-one Pell subgroup.  The exponent is existential: in particular this
does not make the false stronger claim that every residue unit has cube one. -/
theorem exists_j_le_three_quadraticOrderPellUnitEmbedding_pow_two_mul_mem_range_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 3 ∧
      u ^ (2 * j) ∈ Set.range (quadraticOrderPellUnitEmbedding (D : ℤ)) := by
  obtain ⟨j, hjpos, hjle, x, hx⟩ :=
    exists_pow_eq_one_add_two_zsmul_of_quotient_card_eq_four
      (rationalQuadraticRingOfIntegers_modTwo_card (D : ℤ)) u
  exact ⟨j, hjpos, hjle,
    quadraticOrderPellUnitEmbedding_pow_two_mul_mem_range_of_positiveFundamentalDiscriminant_pow_congruent_one
      D hD u j ⟨x, hx⟩⟩

end PellPaper
