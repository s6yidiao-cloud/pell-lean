import Pell.FixedNormResidueTransform
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-!
# A finite Pell-orbit cover from literal coordinate residues

Coordinates are ordered `(d,e)`. Any set on the nonzero level
`v*e^2-u*d^2=h`, even an infinite set, is covered by at most `|h|^2`
full norm-one Pell orbits of representatives chosen from that same set.
Residues need not be invariant along an orbit; only equal residues are used
to construct a transform. Positive cyclic orbits and heights are separate.
-/

namespace PellPaper

/-- Any subset of a fixed nonzero norm level has representatives for a cover
by at most `h.natAbs^2` full Pell-unit orbits. The chosen representatives lie
in the original set, so no height or sign is imposed on an external basepoint. -/
theorem exists_fixedNorm_pellOrbit_representatives
    (u v h : ℤ) (hh : h ≠ 0) (S : Set (ℤ × ℤ))
    (hS : ∀ z ∈ S, v * z.2 ^ 2 - u * z.1 ^ 2 = h) :
    ∃ R : Finset (ℤ × ℤ), (↑R : Set (ℤ × ℤ)) ⊆ S ∧
      R.card ≤ h.natAbs ^ 2 ∧
      ∀ z ∈ S, ∃ r ∈ R, ∃ q : Pell.Solution₁ (u * v),
        z.2 = q.x * r.2 + u * q.y * r.1 ∧
        z.1 = v * q.y * r.2 + q.x * r.1 := by
  classical
  have : NeZero h.natAbs := ⟨by simpa using hh⟩
  let key : (ℤ × ℤ) → ZMod h.natAbs × ZMod h.natAbs :=
    fun z => (z.1, z.2)
  let T : Finset (ZMod h.natAbs × ZMod h.natAbs) :=
    (S.image key).toFinite.toFinset
  have hsurj : S.SurjOn key (↑T : Set _) := by
    intro k hk
    have : k ∈ S.image key := by simpa [T] using hk
    exact this
  obtain ⟨R, hR, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn S T hsurj
  refine ⟨R, hR, ?_, ?_⟩
  · calc
      R.card = (R.image key).card := (Finset.card_image_of_injOn hinj).symm
      _ = T.card := by rw [himage]
      _ ≤ Fintype.card (ZMod h.natAbs × ZMod h.natAbs) := T.card_le_univ
      _ = h.natAbs ^ 2 := by simp [Fintype.card_prod, ZMod.card, pow_two]
  · intro z hz
    have hzkey : key z ∈ R.image key := by
      rw [himage]
      simpa [T] using (show key z ∈ S.image key from ⟨z, hz, rfl⟩)
    obtain ⟨r, hr, hkey⟩ := Finset.mem_image.mp hzkey
    have hd : z.1 ≡ r.1 [ZMOD h] := by
      apply Int.modEq_natAbs.mp
      exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst hkey.symm)
    have he : z.2 ≡ r.2 [ZMOD h] := by
      apply Int.modEq_natAbs.mp
      exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd hkey.symm)
    obtain ⟨q, hqe, hqd⟩ := exists_pell_transform_of_same_norm_modEq
      u v h r.1 r.2 z.1 z.2 hh (hS r (hR hr)) (hS z hz) hd he
    exact ⟨r, hr, q, hqe, hqd⟩

end PellPaper
