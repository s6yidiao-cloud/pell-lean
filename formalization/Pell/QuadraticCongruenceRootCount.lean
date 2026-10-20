import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic

/-!
# Root-count infrastructure for quadratic congruences

The shifted-square congruence estimate needs a uniform bound for square roots
of a unit modulo prime powers.  The odd-prime case follows cleanly from the
cyclicity of the unit group: every nonempty fibre of the squaring homomorphism
is a coset of its kernel, and that kernel has at most two elements.

The two-primary factor and the Chinese-remainder aggregation are kept as
separate lemmas below so that the precise arithmetic boundary remains visible.
-/

namespace PellPaper

noncomputable section

private theorem exists_add_three_eq_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    ∃ j : ℕ, k = j + 3 := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨j, hj.trans (Nat.add_comm 3 j)⟩

/-- In a finite cyclic commutative group, an equation `x^2 = c` has at most
two solutions. -/
theorem natCard_sq_fiber_le_two_of_isCyclic
    (G : Type*) [CommGroup G] [Finite G] [IsCyclic G] (c : G) :
    Nat.card {x : G // x ^ 2 = c} ≤ 2 := by
  classical
  by_cases hroot : ∃ x : G, x ^ 2 = c
  · obtain ⟨a, ha⟩ := hroot
    let f : G →* G := powMonoidHom 2
    have hset : {x : G | x ^ 2 = c} = f ⁻¹' {f a} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      simp [f, powMonoidHom_apply, ha]
    calc
      Nat.card {x : G // x ^ 2 = c} =
          Nat.card (f ⁻¹' {f a}) := by
        exact Nat.card_congr (Equiv.setCongr hset)
      _ = Nat.card f.ker := by
        exact Nat.card_congr (f.fiberEquivKer a)
      _ = (Nat.card G).gcd 2 := by
        exact IsCyclic.card_powMonoidHom_ker G 2
      _ ≤ 2 := Nat.gcd_le_right (Nat.card G) (by norm_num)
  · let f : {x : G // x ^ 2 = c} → Empty := fun x ↦
      (hroot ⟨x.1, x.2⟩).elim
    have hf : Function.Injective f := fun x ↦
      (hroot ⟨x.1, x.2⟩).elim
    have hzero : Nat.card {x : G // x ^ 2 = c} ≤ Nat.card Empty :=
      Nat.card_le_card_of_injective f hf
    simpa using hzero.trans (by norm_num : Nat.card Empty ≤ 2)

/-- An odd-prime-power unit has at most two square roots. -/
theorem natCard_zmod_oddPrimePow_sq_fiber_le_two
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (c : (ZMod (p ^ k))ˣ) :
    Nat.card {x : (ZMod (p ^ k))ˣ // x ^ 2 = c} ≤ 2 := by
  let _ : IsCyclic (ZMod (p ^ k))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  exact natCard_sq_fiber_le_two_of_isCyclic _ c

/-- If the right-hand side is a unit, every ring-valued square root lifts
injectively to a unit-valued square root. -/
theorem natCard_zmod_sq_fiber_le_units_sq_fiber
    {q : ℕ} {c : ZMod q} (hc : IsUnit c) :
    Nat.card {x : ZMod q // x ^ 2 = c} ≤
      Nat.card {u : (ZMod q)ˣ // u ^ 2 = hc.unit} := by
  let liftRoot : {x : ZMod q // x ^ 2 = c} →
      {u : (ZMod q)ˣ // u ^ 2 = hc.unit} := fun x ↦ by
    have hxPow : IsUnit (x.1 ^ 2) := x.2.symm ▸ hc
    have hx : IsUnit x.1 := (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hxPow
    refine ⟨hx.unit, ?_⟩
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    exact x.2
  apply Nat.card_le_card_of_injective liftRoot
  intro x y hxy
  apply Subtype.ext
  have hval := congr_arg (fun u : (ZMod q)ˣ ↦ (u : ZMod q))
    (congr_arg Subtype.val hxy)
  simpa only [liftRoot, IsUnit.unit_spec] using hval

/-- An odd-prime-power unit has at most two square roots already in the
underlying residue ring. -/
theorem natCard_zmod_oddPrimePow_ring_sq_fiber_le_two
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c : ZMod (p ^ k)} (hc : IsUnit c) :
    Nat.card {x : ZMod (p ^ k) // x ^ 2 = c} ≤ 2 := by
  exact (natCard_zmod_sq_fiber_le_units_sq_fiber hc).trans
    (natCard_zmod_oddPrimePow_sq_fiber_le_two hp hp2 hc.unit)

/-- A unit modulo a power of two has at most four unit-valued square roots.
For exponents at most two this follows from the total cardinality.  For
larger exponents, the square-map range contains the square of `5`, whose
order forces the squaring kernel to have cardinality at most four. -/
theorem natCard_zmod_twoPow_units_sq_fiber_le_four
    {k : ℕ} (c : (ZMod (2 ^ k))ˣ) :
    Nat.card {x : (ZMod (2 ^ k))ˣ // x ^ 2 = c} ≤ 4 := by
  classical
  have hsub : Nat.card {x : (ZMod (2 ^ k))ˣ // x ^ 2 = c} ≤
      Nat.card (ZMod (2 ^ k))ˣ :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  by_cases hk : k ≤ 2
  · have hcard : Nat.card (ZMod (2 ^ k))ˣ ≤ 4 := by
      calc
        Nat.card (ZMod (2 ^ k))ˣ ≤ Nat.card (ZMod (2 ^ k)) :=
          Nat.card_le_card_of_injective Units.val Units.val_injective
        _ = 2 ^ k := Nat.card_zmod (2 ^ k)
        _ ≤ 4 := by interval_cases k <;> norm_num
    exact hsub.trans hcard
  · have hk3 : 3 ≤ k := by omega
    obtain ⟨j, hj⟩ := exists_add_three_eq_of_three_le hk3
    subst k
    let G := (ZMod (2 ^ (j + 3)))ˣ
    let f : G →* G := powMonoidHom 2
    let five : G := ZMod.unitOfCoprime 5 (by
      exact (by decide : Nat.Coprime 5 2).pow_right (j + 3))
    have hfiveOrder : orderOf five = 2 ^ (j + 1) := by
      rw [← orderOf_units]
      simpa [five, Nat.add_assoc] using
        ZMod.orderOf_five (j + 1)
    have hfiveSqOrder : orderOf (five ^ 2) = 2 ^ j := by
      rw [orderOf_pow, hfiveOrder]
      simp [pow_succ]
    have hfiveSqMem : five ^ 2 ∈ f.range := ⟨five, rfl⟩
    have hrange : 2 ^ j ≤ Nat.card f.range := by
      rw [← hfiveSqOrder]
      exact f.range.orderOf_le_card (Set.toFinite _) hfiveSqMem
    have hprod : Nat.card f.ker * Nat.card f.range = Nat.card G := by
      simpa only [Subgroup.index_ker] using f.ker.card_mul_index
    have hGcard : Nat.card G = 4 * 2 ^ j := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp [pow_succ]
      ring
    have hker : Nat.card f.ker ≤ 4 := by
      exact Nat.le_of_mul_le_mul_right (by
        calc
          Nat.card f.ker * 2 ^ j ≤ Nat.card f.ker * Nat.card f.range :=
            Nat.mul_le_mul_left _ hrange
          _ = Nat.card G := hprod
          _ = 4 * 2 ^ j := hGcard) (by positivity)
    by_cases hroot : ∃ x : G, x ^ 2 = c
    · obtain ⟨a, ha⟩ := hroot
      have hset : {x : G | x ^ 2 = c} = f ⁻¹' {f a} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        simp [f, powMonoidHom_apply, ha]
      calc
        Nat.card {x : G // x ^ 2 = c} = Nat.card (f ⁻¹' {f a}) :=
          Nat.card_congr (Equiv.setCongr hset)
        _ = Nat.card f.ker := Nat.card_congr (f.fiberEquivKer a)
        _ ≤ 4 := hker
    · let emptyMap : {x : G // x ^ 2 = c} → Empty := fun x ↦
        (hroot ⟨x.1, x.2⟩).elim
      have hemptyInjective : Function.Injective emptyMap := fun x ↦
        (hroot ⟨x.1, x.2⟩).elim
      have hzero : Nat.card {x : G // x ^ 2 = c} ≤ Nat.card Empty :=
        Nat.card_le_card_of_injective emptyMap hemptyInjective
      exact hzero.trans (by norm_num)

/-- A unit modulo a power of two has at most four roots in the underlying
residue ring. -/
theorem natCard_zmod_twoPow_ring_sq_fiber_le_four
    {k : ℕ} {c : ZMod (2 ^ k)} (hc : IsUnit c) :
    Nat.card {x : ZMod (2 ^ k) // x ^ 2 = c} ≤ 4 := by
  exact (natCard_zmod_sq_fiber_le_units_sq_fiber hc).trans
    (natCard_zmod_twoPow_units_sq_fiber_le_four hc.unit)

end


end PellPaper
