import Pell.RankTwoHermiteSubmodule
import Mathlib.GroupTheory.Index

/-!
# Hermite classification of finite-index rank-two integer submodules

This file constructs the normalized triangular generators directly from a
finite-index submodule of `ℤ²`.  It does not use a pre-existing normal-form
decomposition: the diagonal entries are the least positive horizontal and
vertical coordinates, and Euclidean division gives both generation and the
normalization of the upper-right entry.
-/

namespace PellPaper

open Matrix

private theorem rankTwo_horizontal_generator
    (N : Submodule ℤ (Fin 2 → ℤ))
    (hN : N.toAddSubgroup.index ≠ 0) :
    ∃ a : ℕ, 0 < a ∧ ![(a : ℤ), 0] ∈ N ∧
      ∀ z : ℤ, ![z, 0] ∈ N → (a : ℤ) ∣ z := by
  classical
  obtain ⟨n, hn, -, hnN⟩ :=
    N.toAddSubgroup.exists_nsmul_mem_of_index_ne_zero hN ![(1 : ℤ), 0]
  have hex : ∃ n : ℕ, 0 < n ∧ ![(n : ℤ), 0] ∈ N := by
    refine ⟨n, hn, ?_⟩
    simpa using hnN
  let a : ℕ := Nat.find hex
  have ha := Nat.find_spec hex
  refine ⟨a, ha.1, ha.2, ?_⟩
  intro z hz
  let r : ℤ := z % (a : ℤ)
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha.1
  have hr0 : 0 ≤ r := Int.emod_nonneg _ haZ.ne'
  have hra : r < (a : ℤ) := Int.emod_lt_of_pos _ haZ
  have hrem : ![r, 0] ∈ N := by
    have hsub := N.sub_mem hz (N.smul_mem (z / (a : ℤ)) ha.2)
    convert hsub using 1
    ext i
    fin_cases i
    · dsimp [r]
      change z % (a : ℤ) = z - z / (a : ℤ) * (a : ℤ)
      have hdiv := Int.ediv_mul_add_emod z (a : ℤ)
      omega
    · simp
  have hr : r = 0 := by
    by_contra hrne
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
    have hrnat : 0 < r.natAbs := Int.natAbs_pos.mpr hrne
    have hrcast : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hr0
    have hrlt : r.natAbs < a := by
      rw [← hrcast] at hra
      exact_mod_cast hra
    have hpred : 0 < r.natAbs ∧ ![(r.natAbs : ℤ), 0] ∈ N := by
      refine ⟨hrnat, ?_⟩
      simpa [hrcast] using hrem
    exact (Nat.find_min hex hrlt) hpred
  exact Int.dvd_iff_emod_eq_zero.mpr hr

private theorem rankTwo_vertical_generator
    (N : Submodule ℤ (Fin 2 → ℤ))
    (hN : N.toAddSubgroup.index ≠ 0) :
    ∃ d : ℕ, 0 < d ∧
      (∃ w : Fin 2 → ℤ, w ∈ N ∧ w 1 = (d : ℤ)) ∧
      ∀ v : Fin 2 → ℤ, v ∈ N → (d : ℤ) ∣ v 1 := by
  classical
  obtain ⟨n, hn, -, hnN⟩ :=
    N.toAddSubgroup.exists_nsmul_mem_of_index_ne_zero hN ![(0 : ℤ), 1]
  have hex : ∃ n : ℕ, 0 < n ∧
      ∃ w : Fin 2 → ℤ, w ∈ N ∧ w 1 = (n : ℤ) := by
    refine ⟨n, hn, ![(n : ℤ) • 0, (n : ℤ) • 1], ?_, by simp⟩
    simpa using hnN
  let d : ℕ := Nat.find hex
  have hd := Nat.find_spec hex
  refine ⟨d, hd.1, hd.2, ?_⟩
  intro v hv
  obtain ⟨w, hwN, hw1⟩ := hd.2
  let r : ℤ := v 1 % (d : ℤ)
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd.1
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hdZ.ne'
  have hrd : r < (d : ℤ) := Int.emod_lt_of_pos _ hdZ
  let u : Fin 2 → ℤ := v - (v 1 / (d : ℤ)) • w
  have huN : u ∈ N := N.sub_mem hv (N.smul_mem _ hwN)
  have hu1 : u 1 = r := by
    dsimp [u, r]
    have hdiv := Int.ediv_mul_add_emod (v 1) (d : ℤ)
    calc
      v 1 - v 1 / (d : ℤ) * w 1 =
          v 1 - v 1 / (d : ℤ) * (d : ℤ) := by rw [hw1]
      _ = v 1 % (d : ℤ) := by omega
  have hr : r = 0 := by
    by_contra hrne
    have hrnat : 0 < r.natAbs := Int.natAbs_pos.mpr hrne
    have hrcast : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hr0
    have hrlt : r.natAbs < d := by
      rw [← hrcast] at hrd
      exact_mod_cast hrd
    have hpred : 0 < r.natAbs ∧
        ∃ w : Fin 2 → ℤ, w ∈ N ∧ w 1 = (r.natAbs : ℤ) := by
      exact ⟨hrnat, u, huN, hu1.trans hrcast.symm⟩
    exact (Nat.find_min hex hrlt) hpred
  exact Int.dvd_iff_emod_eq_zero.mpr hr

/-- Every finite-index submodule of `ℤ²` has normalized upper-triangular
Hermite generators. -/
theorem exists_rankTwoHermiteSubmodule_of_index_ne_zero
    (N : Submodule ℤ (Fin 2 → ℤ))
    (hN : N.toAddSubgroup.index ≠ 0) :
    ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
      ∃ b : ℕ, b < a ∧
        N = rankTwoHermiteSubmodule (a : ℤ) (b : ℤ) (d : ℤ) := by
  classical
  obtain ⟨a, ha, haN, ha_dvd⟩ := rankTwo_horizontal_generator N hN
  obtain ⟨d, hd, ⟨w, hwN, hw1⟩, hd_dvd⟩ := rankTwo_vertical_generator N hN
  let r : ℤ := w 0 % (a : ℤ)
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hr0 : 0 ≤ r := Int.emod_nonneg _ haZ.ne'
  have hra : r < (a : ℤ) := Int.emod_lt_of_pos _ haZ
  let b : ℕ := r.natAbs
  have hbcast : (b : ℤ) = r := Int.natAbs_of_nonneg hr0
  have hb : b < a := by
    rw [← hbcast] at hra
    exact_mod_cast hra
  let w' : Fin 2 → ℤ := w - (w 0 / (a : ℤ)) • ![(a : ℤ), 0]
  have hw'N : w' ∈ N := N.sub_mem hwN (N.smul_mem _ haN)
  have hw'eq : w' = ![(b : ℤ), (d : ℤ)] := by
    ext i
    fin_cases i
    · dsimp [w']
      change w 0 - w 0 / (a : ℤ) * (a : ℤ) = (b : ℤ)
      rw [hbcast]
      have hdiv := Int.ediv_mul_add_emod (w 0) (a : ℤ)
      dsimp [r]
      omega
    · change w 1 - w 0 / (a : ℤ) * 0 = (d : ℤ)
      simpa using hw1
  have hbN : ![(b : ℤ), (d : ℤ)] ∈ N := hw'eq ▸ hw'N
  refine ⟨a, d, ha, hd, b, hb, ?_⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨y, hy⟩ := hd_dvd v hv
    have hsub : v - y • ![(b : ℤ), (d : ℤ)] ∈ N :=
      N.sub_mem hv (N.smul_mem y hbN)
    have hsubeq : v - y • ![(b : ℤ), (d : ℤ)] =
        ![v 0 - (b : ℤ) * y, 0] := by
      ext i
      fin_cases i
      · simp [mul_comm]
      · simp [hy, mul_comm]
    have hhoriz : ![v 0 - (b : ℤ) * y, 0] ∈ N := hsubeq ▸ hsub
    obtain ⟨x, hx⟩ := ha_dvd _ hhoriz
    rw [mem_rankTwoHermiteSubmodule_iff]
    refine ⟨x, y, ?_, hy⟩
    omega
  · intro v hv
    rw [mem_rankTwoHermiteSubmodule_iff] at hv
    obtain ⟨x, y, h0, h1⟩ := hv
    have hcomb := N.add_mem (N.smul_mem x haN) (N.smul_mem y hbN)
    convert hcomb using 1
    ext i
    fin_cases i
    · simp [h0, mul_comm]
    · simp [h1, mul_comm]

/-- Positive triangular presentations whose upper-right entries lie in the
standard half-open intervals are unique. -/
theorem rankTwoHermiteSubmodule_normalized_unique
    {a b d a' b' d' : ℕ}
    (ha : 0 < a) (hb : b < a) (hd : 0 < d)
    (ha' : 0 < a') (hb' : b' < a') (hd' : 0 < d')
    (hEq : rankTwoHermiteSubmodule (a : ℤ) (b : ℤ) (d : ℤ) =
      rankTwoHermiteSubmodule (a' : ℤ) (b' : ℤ) (d' : ℤ)) :
    a = a' ∧ b = b' ∧ d = d' := by
  have haZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have horizontal_dvd : ∀ {A B D : ℕ}, 0 < D → ∀ {z : ℤ},
      ![z, 0] ∈ rankTwoHermiteSubmodule (A : ℤ) (B : ℤ) (D : ℤ) →
        (A : ℤ) ∣ z := by
    intro A B D hD z hz
    rw [mem_rankTwoHermiteSubmodule_iff] at hz
    obtain ⟨x, y, h0, h1⟩ := hz
    have hDZ : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
    have hy : y = 0 := by
      exact (mul_eq_zero.mp h1.symm).resolve_left hDZ
    exact ⟨x, by simpa [hy] using h0⟩
  have vertical_dvd : ∀ {A B D : ℕ} {v : Fin 2 → ℤ},
      v ∈ rankTwoHermiteSubmodule (A : ℤ) (B : ℤ) (D : ℤ) →
        (D : ℤ) ∣ v 1 := by
    intro A B D v hv
    rw [mem_rankTwoHermiteSubmodule_iff] at hv
    obtain ⟨x, y, h0, h1⟩ := hv
    exact ⟨y, h1⟩
  have ha'dvdZ : (a' : ℤ) ∣ (a : ℤ) := by
    apply horizontal_dvd hd'
    rw [← hEq]
    exact first_mem_rankTwoHermiteSubmodule _ _ _
  have hadivZ : (a : ℤ) ∣ (a' : ℤ) := by
    apply horizontal_dvd hd
    rw [hEq]
    exact first_mem_rankTwoHermiteSubmodule _ _ _
  have ha'dvd : a' ∣ a := by exact_mod_cast ha'dvdZ
  have hadiv : a ∣ a' := by exact_mod_cast hadivZ
  have haa' : a = a' := Nat.dvd_antisymm hadiv ha'dvd
  have hd'dvdZ : (d' : ℤ) ∣ (d : ℤ) := by
    have hm : ![(b : ℤ), (d : ℤ)] ∈
        rankTwoHermiteSubmodule (a' : ℤ) (b' : ℤ) (d' : ℤ) := by
      rw [← hEq]
      exact second_mem_rankTwoHermiteSubmodule _ _ _
    simpa using
      (vertical_dvd (A := a') (B := b') (D := d')
        (v := ![(b : ℤ), (d : ℤ)]) hm)
  have hddivZ : (d : ℤ) ∣ (d' : ℤ) := by
    have hm : ![(b' : ℤ), (d' : ℤ)] ∈
        rankTwoHermiteSubmodule (a : ℤ) (b : ℤ) (d : ℤ) := by
      rw [hEq]
      exact second_mem_rankTwoHermiteSubmodule _ _ _
    simpa using
      (vertical_dvd (A := a) (B := b) (D := d)
        (v := ![(b' : ℤ), (d' : ℤ)]) hm)
  have hd'dvd : d' ∣ d := by exact_mod_cast hd'dvdZ
  have hddiv : d ∣ d' := by exact_mod_cast hddivZ
  have hdd' : d = d' := Nat.dvd_antisymm hddiv hd'dvd
  subst a'
  subst d'
  have hmem : ![(b : ℤ), (d : ℤ)] ∈
      rankTwoHermiteSubmodule (a : ℤ) (b' : ℤ) (d : ℤ) := by
    rw [← hEq]
    exact second_mem_rankTwoHermiteSubmodule _ _ _
  rw [mem_rankTwoHermiteSubmodule_iff] at hmem
  obtain ⟨x, y, h0, h1⟩ := hmem
  have h0' : (b : ℤ) = (a : ℤ) * x + (b' : ℤ) * y := by
    simpa using h0
  have h1' : (d : ℤ) = (d : ℤ) * y := by
    simpa using h1
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hy : y = 1 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hdZ
    calc
      (d : ℤ) * (y - 1) = (d : ℤ) * y - (d : ℤ) := by ring
      _ = 0 := by omega
  have habdvd : (a : ℤ) ∣ (b : ℤ) - (b' : ℤ) := by
    refine ⟨x, ?_⟩
    rw [hy] at h0'
    omega
  have habs : |(b : ℤ) - (b' : ℤ)| < (a : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : (b : ℤ) - (b' : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd habdvd habs
  have hbb' : b = b' := by exact_mod_cast (sub_eq_zero.mp hzero)
  exact ⟨rfl, hbb', rfl⟩

end PellPaper
