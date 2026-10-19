import Pell.RealQuadraticFieldOddClassSum
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The odd part as a count of actual ideal classes

The manuscript defines the odd class number as the number of ideal classes
of odd order. The headline sum uses `ordCompl[2]` of the class-group order.
This module identifies those two descriptions in every finite commutative
group, then applies the result to real quadratic ideal class groups.
-/

namespace PellPaper

open NumberField

noncomputable section

private theorem card_oddOrderElements (G : Type*) [CommGroup G] [Finite G] :
    Nat.card {g : G // Odd (orderOf g)} = ordCompl[2] (Nat.card G) := by
  classical
  let P : Sylow 2 G := default
  obtain ⟨H, hHP⟩ :=
    Subgroup.exists_left_complement'_of_coprime (N := (P : Subgroup G))
      P.card_coprime_index
  have hPCard : Nat.card (P : Subgroup G) = ordProj[2] (Nat.card G) :=
    P.card_eq_multiplicity
  have hHCard : Nat.card H = ordCompl[2] (Nat.card G) := by
    apply mul_right_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
    calc
      Nat.card H * ordProj[2] (Nat.card G) = Nat.card G := by
        simpa only [hPCard] using hHP.card_mul_card
      _ = ordCompl[2] (Nat.card G) * ordProj[2] (Nat.card G) := by
        rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  have hHOdd : Odd (Nat.card H) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have htwo : (2 : ℕ) ∣ Nat.card H := even_iff_two_dvd.mp he
    rw [hHCard] at htwo
    exact Nat.not_dvd_ordCompl Nat.prime_two Nat.card_pos.ne' htwo
  have hmem (g : G) : g ∈ H ↔ Odd (orderOf g) := by
    constructor
    · intro hg
      exact hHOdd.of_dvd_nat (Subgroup.orderOf_dvd_natCard H hg)
    · intro hodd
      let q : G ⧸ H := (QuotientGroup.mk' H) g
      have hqG : orderOf q ∣ orderOf g := orderOf_map_dvd (QuotientGroup.mk' H) g
      have hqP : orderOf q ∣ Nat.card (P : Subgroup G) := by
        have hq : orderOf q ∣ Nat.card (G ⧸ H) := orderOf_dvd_natCard q
        simpa only [← H.index_eq_card, hHP.symm.index_eq_card] using hq
      have hnot2 : ¬(2 : ℕ) ∣ orderOf g := by
        intro hd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
      have hcop : (orderOf g).Coprime (Nat.card (P : Subgroup G)) := by
        rw [hPCard]
        exact Nat.prime_two.coprime_pow_of_not_dvd hnot2
      have hq1 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hqG hqP
      exact (QuotientGroup.eq_one_iff g).mp
        (by simpa only [q, QuotientGroup.mk'_apply] using (orderOf_eq_one_iff.mp hq1))
  let e : H ≃ {g : G // Odd (orderOf g)} :=
    { toFun := fun g => ⟨g.1, (hmem g.1).mp g.2⟩
      invFun := fun g => ⟨g.1, (hmem g.1).mpr g.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact (Nat.card_congr e).symm.trans hHCard

/-- The `ordCompl[2]` summand in the odd class-average theorem counts exactly
the elements of odd order in the ordinary ideal class group of a real
quadratic field. -/
theorem realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses
    (K : RealQuadraticFieldClass) (F : RealQuadraticField) (hFK : F.toClass = K) :
    realQuadraticFieldOddClassNumber K =
      Nat.card {c : ClassGroup (𝓞 F) // Odd (orderOf c)} := by
  subst K
  unfold realQuadraticFieldOddClassNumber
  rw [realQuadraticFieldClassNumber_toClass]
  simpa only [NumberField.classNumber, Nat.card_eq_fintype_card] using
    (card_oddOrderElements (ClassGroup (𝓞 F))).symm

end

end PellPaper
