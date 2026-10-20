import Pell.NonprincipalDirichletPolyaVinogradov

/-!
# Shifted windows for nonprincipal Dirichlet characters

The existing all-nonprincipal Pólya--Vinogradov theorem bounds natural
prefixes.  Taking the difference of two prefixes gives a uniform bound for
an arbitrary translated range in `ZMod q`.  The translation is represented
by an actual residue, so wraparound and windows longer than the modulus are
included.
-/

open scoped BigOperators

namespace PellPaper

private theorem nonprincipalDirichletCharacter_range_norm_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, chi (n : ZMod q)‖ ≤
      2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hq1 : 1 < q := by
    have hqpos : 0 < q := NeZero.pos q
    by_contra hnot
    have hqeq : q = 1 := by omega
    subst q
    exact hchi (Subsingleton.elim chi 1)
  let _ : Fact (1 < q) := ⟨hq1⟩
  have hrange :
      (∑ n ∈ Finset.range N, chi (n : ZMod q)) =
        ∑ n ∈ Finset.Icc 1 (N - 1), chi (n : ZMod q) := by
    rcases N with _ | N
    · simp
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hzero : chi ((0 : ℕ) : ZMod q) = 0 := by
      simpa only [Nat.cast_zero] using chi.map_zero
    rw [hzero, add_zero]
    have hIco := Finset.sum_Ico_eq_sum_range
      (fun n : ℕ => chi (n : ZMod q)) 1 (N + 1)
    have hsets : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hsets] at hIco
    simpa [add_comm] using hIco.symm
  rw [hrange]
  exact nonprincipalDirichletCharacter_prefix_norm_le chi hchi (N - 1)

/-- Every residue-shifted natural range of a nonprincipal complex Dirichlet
character satisfies a uniform Pólya--Vinogradov bound.  The range can be
empty or longer than the modulus. -/
theorem nonprincipalDirichletCharacter_shifted_range_norm_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (c : ZMod q) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, chi ((n : ZMod q) + c)‖ ≤
      4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hsum :
      (∑ n ∈ Finset.range L, chi ((n : ZMod q) + c)) =
        ∑ n ∈ Finset.Ico c.val (c.val + L), chi (n : ZMod q) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    rw [add_comm]
  rw [hsum]
  have hIco :
      (∑ n ∈ Finset.Ico c.val (c.val + L), chi (n : ZMod q)) =
        (∑ n ∈ Finset.range (c.val + L), chi (n : ZMod q)) -
          ∑ n ∈ Finset.range c.val, chi (n : ZMod q) :=
    Finset.sum_Ico_eq_sub (fun n : ℕ => chi (n : ZMod q))
      (Nat.le_add_right c.val L)
  rw [hIco]
  calc
    ‖(∑ n ∈ Finset.range (c.val + L), chi (n : ZMod q)) -
        ∑ n ∈ Finset.range c.val, chi (n : ZMod q)‖ ≤
        ‖∑ n ∈ Finset.range (c.val + L), chi (n : ZMod q)‖ +
          ‖∑ n ∈ Finset.range c.val, chi (n : ZMod q)‖ := norm_sub_le _ _
    _ ≤ (2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))) +
          (2 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))) :=
      add_le_add
        (nonprincipalDirichletCharacter_range_norm_le chi hchi _)
        (nonprincipalDirichletCharacter_range_norm_le chi hchi _)
    _ = 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by ring

end PellPaper
