import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite exponential windows on arbitrary cyclic residue rings

Geometric summation and Jordan's sine inequality bound each nonzero
frequency of a finite interval. Summing the reciprocal distances to both
endpoints gives a harmonic, hence logarithmic, bound. All levels are
allowed, including composite levels and the empty frequency set at level
one; shifts and interval lengths are unrestricted.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

private theorem norm_geom_sum_le_two_div
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

private theorem two_mul_mul_one_sub_le_sin_pi_mul
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * t * (1 - t) ≤ Real.sin (Real.pi * t) := by
  by_cases ht : t ≤ 1 / 2
  · have hs := Real.le_sin_mul (x := 2 * t) (by linarith) (by linarith)
    have harg : Real.pi / 2 * (2 * t) = Real.pi * t := by ring
    rw [harg] at hs
    nlinarith [sq_nonneg t]
  · have hs := Real.le_sin_mul (x := 2 * (1 - t)) (by linarith) (by linarith)
    have harg : Real.pi / 2 * (2 * (1 - t)) = Real.pi - Real.pi * t := by ring
    rw [harg, Real.sin_pi_sub] at hs
    nlinarith [sq_nonneg (1 - t)]

private theorem stdAddChar_sub_one_norm_lower
    {q : ℕ} [NeZero q] (k : ℕ) (hk0 : 0 < k) (hkq : k < q) :
    4 * ((k : ℝ) / q) * (1 - (k : ℝ) / q) ≤
      ‖ZMod.stdAddChar (k : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ht0 : 0 ≤ (k : ℝ) / q := by positivity
  have ht1 : (k : ℝ) / q ≤ 1 := (div_le_one hq).mpr (by exact_mod_cast hkq.le)
  have hs := two_mul_mul_one_sub_le_sin_pi_mul ((k : ℝ) / q) ht0 ht1
  have he : ZMod.stdAddChar (k : ZMod q) =
      Complex.exp (Complex.I * (((2 * Real.pi * ((k : ℝ) / q) : ℝ) : ℂ))) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have ht : 2 * Real.pi * ((k : ℝ) / q) / 2 = Real.pi * ((k : ℝ) / q) := by ring
  rw [ht, Real.norm_eq_abs]
  have hsnonneg : 0 ≤ Real.sin (Real.pi * ((k : ℝ) / q)) :=
    (by positivity : 0 ≤ 2 * ((k : ℝ) / q) * (1 - (k : ℝ) / q)).trans hs
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hsnonneg)]
  nlinarith

/-- Every nonzero residue frequency has a finite-window norm bounded by
the two reciprocal endpoint distances. The bound is uniform in the shift
and length of the window. -/
theorem norm_stdAddChar_sum_range_le
    {q : ℕ} [NeZero q] (k : ℕ) (hk0 : 0 < k) (hkq : k < q)
    (a : ZMod q) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod q) * (a + (n : ZMod q)))‖ ≤
      (q : ℝ) / (2 * k) + (q : ℝ) / (2 * (q - k : ℕ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hqk : (0 : ℝ) < q - (k : ℝ) := sub_pos.mpr (by exact_mod_cast hkq)
  have hphase : 0 < (k : ℝ) / q ∧ (k : ℝ) / q < 1 :=
    ⟨div_pos hk hq, (div_lt_one hq).mpr (by exact_mod_cast hkq)⟩
  have hlower := stdAddChar_sub_one_norm_lower k hk0 hkq
  have hdenpos : 0 < 4 * ((k : ℝ) / q) * (1 - (k : ℝ) / q) :=
    mul_pos (mul_pos (by norm_num) hphase.1) (sub_pos.mpr hphase.2)
  have hz1 : ZMod.stdAddChar (k : ZMod q) ≠ 1 := by
    intro hz
    rw [hz, sub_self, norm_zero] at hlower
    linarith
  have hz : ‖ZMod.stdAddChar (k : ZMod q)‖ = 1 := by
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  have hsum : (∑ n ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod q) * (a + (n : ZMod q)))) =
      ZMod.stdAddChar ((k : ZMod q) * a) *
        ∑ n ∈ Finset.range L, (ZMod.stdAddChar (k : ZMod q)) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_add, AddChar.map_add_eq_mul]
    congr 1
    rw [mul_comm (k : ZMod q), ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [hsum, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
  calc
    ‖∑ n ∈ Finset.range L, ZMod.stdAddChar (k : ZMod q) ^ n‖ ≤
        2 / ‖ZMod.stdAddChar (k : ZMod q) - 1‖ := norm_geom_sum_le_two_div _ hz hz1 L
    _ ≤ 2 / (4 * ((k : ℝ) / q) * (1 - (k : ℝ) / q)) :=
      div_le_div_of_nonneg_left (by norm_num) hdenpos hlower
    _ = (q : ℝ) / (2 * k) + (q : ℝ) / (2 * (q - k : ℕ)) := by
      rw [Nat.cast_sub hkq.le]
      field_simp
      ring

/-- The total finite exponential-window norm over the nonzero frequencies
is bounded by a harmonic logarithm, uniformly in shift and window length. -/
theorem sum_norm_stdAddChar_sum_range_le
    {q : ℕ} [NeZero q] (a : ZMod q) (L : ℕ) :
    (∑ k ∈ Finset.Ico 1 q,
      ‖∑ n ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod q) * (a + (n : ZMod q)))‖) ≤
      (q : ℝ) * (1 + Real.log q) := by
  classical
  have hreflect : (∑ k ∈ Finset.Ico 1 q, (q : ℝ) / (2 * (q - k : ℕ))) =
      ∑ k ∈ Finset.Ico 1 q, (q : ℝ) / (2 * k) := by
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using
      (Finset.sum_Ico_reflect (fun k : ℕ => (q : ℝ) / (2 * k)) 1
        (m := q) (n := q) (Nat.le_succ q))
  have hfactor : (∑ k ∈ Finset.Ico 1 q, (q : ℝ) / (2 * k)) =
      ((q : ℝ) / 2) * ∑ k ∈ Finset.Ico 1 q, (k : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hharm : (∑ k ∈ Finset.Ico 1 q, (k : ℝ)⁻¹) ≤ (harmonic q : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩
    · intro k _ _
      positivity
  calc
    (∑ k ∈ Finset.Ico 1 q,
      ‖∑ n ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod q) * (a + (n : ZMod q)))‖) ≤
        ∑ k ∈ Finset.Ico 1 q, ((q : ℝ) / (2 * k) + (q : ℝ) / (2 * (q - k : ℕ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_stdAddChar_sum_range_le k
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp hk).1)
        (Finset.mem_Ico.mp hk).2 a L
    _ = (q : ℝ) * ∑ k ∈ Finset.Ico 1 q, (k : ℝ)⁻¹ := by
      rw [Finset.sum_add_distrib, hreflect, hfactor]
      ring
    _ ≤ (q : ℝ) * (harmonic q : ℝ) := mul_le_mul_of_nonneg_left hharm (Nat.cast_nonneg q)
    _ ≤ (q : ℝ) * (1 + Real.log q) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (Nat.cast_nonneg q)

end
end PellPaper
