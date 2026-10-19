import Mathlib.Data.Fintype.Card

/-!
# Extending a finite column embedding by one fresh column

Given an embedding of `Fin r` into a finite type with strictly more than `r`
elements, this module chooses one point outside its range and appends it as
the final coordinate of an embedding of `Fin (r + 1)`.  It is purely finite
bookkeeping: no matrix, rank, or determinant statement is made here.
-/

namespace PellPaper

/-- A finite ambient type with more than `r` elements contains a point outside
the range of any embedding of `Fin r`. -/
theorem exists_extraColumn_not_mem_range {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) :
    ∃ x : κ, x ∉ Set.range e := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective e := by
    intro x
    obtain ⟨i, hi⟩ := h x
    exact ⟨i, hi⟩
  have hle : Fintype.card κ ≤ Fintype.card (Fin r) :=
    Fintype.card_le_of_surjective e hsurj
  exact (not_le_of_gt hcard) (by simpa using hle)

/-- The chosen additional column outside the range of `e`. -/
noncomputable def extraColumn {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) : κ :=
  Classical.choose (exists_extraColumn_not_mem_range e hcard)

/-- The chosen additional column is genuinely fresh. -/
theorem extraColumn_not_mem_range {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) :
    extraColumn e hcard ∉ Set.range e :=
  Classical.choose_spec (exists_extraColumn_not_mem_range e hcard)

/-- The function obtained by appending the chosen fresh column after `e`. -/
noncomputable def extendEmbeddingExtraColumnFun {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) : Fin r.succ → κ :=
  Fin.lastCases (extraColumn e hcard) e

@[simp]
theorem extendEmbeddingExtraColumnFun_castSucc {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) (j : Fin r) :
    extendEmbeddingExtraColumnFun e hcard j.castSucc = e j := by
  simp [extendEmbeddingExtraColumnFun]

@[simp]
theorem extendEmbeddingExtraColumnFun_last {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) :
    extendEmbeddingExtraColumnFun e hcard (Fin.last r) = extraColumn e hcard := by
  simp [extendEmbeddingExtraColumnFun]

/-- Appending a fresh column to an embedding remains injective. -/
theorem extendEmbeddingExtraColumnFun_injective {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) :
    Function.Injective (extendEmbeddingExtraColumnFun e hcard) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with hi | hi
  · obtain ⟨i', hi⟩ := hi
    rw [hi] at hij ⊢
    rcases Fin.eq_castSucc_or_eq_last j with hj | hj
    · obtain ⟨j', hj⟩ := hj
      rw [hj] at hij ⊢
      exact congrArg Fin.castSucc (e.injective (by
        simpa only [extendEmbeddingExtraColumnFun_castSucc] using hij))
    · exfalso
      rw [hj] at hij
      apply extraColumn_not_mem_range e hcard
      refine ⟨i', ?_⟩
      simpa only [extendEmbeddingExtraColumnFun_castSucc,
        extendEmbeddingExtraColumnFun_last] using hij
  · rw [hi] at hij ⊢
    rcases Fin.eq_castSucc_or_eq_last j with hj | hj
    · obtain ⟨j', hj⟩ := hj
      rw [hj] at hij ⊢
      exfalso
      apply extraColumn_not_mem_range e hcard
      refine ⟨j', ?_⟩
      simpa only [extendEmbeddingExtraColumnFun_castSucc,
        extendEmbeddingExtraColumnFun_last] using hij.symm
    · simp [hj]

/-- Extend `e` by appending its chosen fresh column as the last coordinate. -/
noncomputable def extendEmbeddingExtraColumn {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) : Fin r.succ ↪ κ :=
  ⟨extendEmbeddingExtraColumnFun e hcard,
    extendEmbeddingExtraColumnFun_injective e hcard⟩

/-- The one-column extension agrees exactly with `e` on its original
coordinates. -/
@[simp]
theorem extendEmbeddingExtraColumn_castSucc {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) (j : Fin r) :
    extendEmbeddingExtraColumn e hcard j.castSucc = e j := by
  exact extendEmbeddingExtraColumnFun_castSucc e hcard j

/-- The final coordinate of the extension is its chosen extra column. -/
@[simp]
theorem extendEmbeddingExtraColumn_last {r : ℕ} {κ : Type*} [Fintype κ]
    (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) :
    extendEmbeddingExtraColumn e hcard (Fin.last r) = extraColumn e hcard := by
  exact extendEmbeddingExtraColumnFun_last e hcard

/-- The final coordinate of the extension is outside the range of the
original embedding. -/
theorem extendEmbeddingExtraColumn_last_not_mem_range {r : ℕ} {κ : Type*}
    [Fintype κ] (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) :
    extendEmbeddingExtraColumn e hcard (Fin.last r) ∉ Set.range e := by
  rw [extendEmbeddingExtraColumn_last]
  exact extraColumn_not_mem_range e hcard

/-- In particular, the appended last column differs from every original
coordinate of the extended embedding. -/
theorem extendEmbeddingExtraColumn_last_ne_castSucc {r : ℕ} {κ : Type*}
    [Fintype κ] (e : Fin r ↪ κ) (hcard : r < Fintype.card κ) (j : Fin r) :
    extendEmbeddingExtraColumn e hcard (Fin.last r) ≠
      extendEmbeddingExtraColumn e hcard j.castSucc := by
  intro h
  apply extendEmbeddingExtraColumn_last_not_mem_range e hcard
  exact ⟨j, by simpa using h.symm⟩

end PellPaper
