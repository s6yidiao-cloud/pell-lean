import Pell.ZModExponentialWindowBound
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Two-dimensional Fourier completion on cyclic residue rings

This module defines the literal negative, unnormalised double Fourier
transform on `(ZMod q)^2`.  Two applications of the actual Mathlib inverse
DFT, together with the finite exponential-window estimate, bound every
shifted rectangle.  Composite levels, level one, empty rectangles, and
windows longer than the level are all included.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The literal negative, unnormalised two-dimensional Fourier transform. -/
def zmodFourier2 {q : ℕ} [NeZero q]
    (f : ZMod q → ZMod q → ℂ) (k l : ZMod q) : ℂ :=
  ∑ x : ZMod q, ∑ y : ZMod q,
    f x y * ZMod.stdAddChar (-k * x - l * y)

private def zmodWindow {q : ℕ} [NeZero q]
    (a : ZMod q) (L : ℕ) (k : ZMod q) : ℂ :=
  ∑ n ∈ Finset.range L,
    ZMod.stdAddChar (k * (a + (n : ZMod q)))

private theorem zmodWindow_zero {q : ℕ} [NeZero q]
    (a : ZMod q) (L : ℕ) : zmodWindow a L 0 = L := by
  simp [zmodWindow]

private theorem zmodFourier2_eq_iteratedDft {q : ℕ} [NeZero q]
    (f : ZMod q → ZMod q → ℂ) (k l : ZMod q) :
    zmodFourier2 f k l = ZMod.dft (fun x => ZMod.dft (f x) l) k := by
  classical
  simp only [zmodFourier2, ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  rw [show -k * x - l * y = -(x * k) + -(y * l) by ring,
    AddChar.map_add_eq_mul]
  ring

private theorem sum_range_eq_inv_mul_dft_window
    {q : ℕ} [NeZero q] (g : ZMod q → ℂ) (a : ZMod q) (L : ℕ) :
    (∑ n ∈ Finset.range L, g (a + (n : ZMod q))) =
      (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.dft g k * zmodWindow a L k := by
  classical
  have hinv (x : ZMod q) : g x =
      (q : ℂ)⁻¹ * ∑ k : ZMod q, ZMod.stdAddChar (k * x) * ZMod.dft g k := by
    have h := congrFun (ZMod.dft.symm_apply_apply g) x
    simpa only [ZMod.invDFT_apply, smul_eq_mul] using h.symm
  calc
    (∑ n ∈ Finset.range L, g (a + (n : ZMod q))) =
        ∑ n ∈ Finset.range L,
          ((q : ℂ)⁻¹ * ∑ k : ZMod q,
            ZMod.stdAddChar (k * (a + (n : ZMod q))) * ZMod.dft g k) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [hinv]
    _ = (q : ℂ)⁻¹ * ∑ n ∈ Finset.range L,
          ∑ k : ZMod q,
            ZMod.stdAddChar (k * (a + (n : ZMod q))) * ZMod.dft g k := by
      rw [Finset.mul_sum]
    _ = (q : ℂ)⁻¹ * ∑ k : ZMod q,
          ZMod.dft g k * zmodWindow a L k := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [zmodWindow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

private theorem sum_box_fourier_identity
    {q : ℕ} [NeZero q] (f : ZMod q → ZMod q → ℂ)
    (a b : ZMod q) (L₁ L₂ : ℕ) :
    (∑ i ∈ Finset.range L₁, ∑ j ∈ Finset.range L₂,
        f (a + (i : ZMod q)) (b + (j : ZMod q))) =
      (q : ℂ)⁻¹ * (q : ℂ)⁻¹ *
        ∑ l : ZMod q, ∑ k : ZMod q,
          zmodFourier2 f k l * zmodWindow a L₁ k * zmodWindow b L₂ l := by
  classical
  calc
    _ = ∑ i ∈ Finset.range L₁,
          ((q : ℂ)⁻¹ * ∑ l : ZMod q,
            ZMod.dft (f (a + (i : ZMod q))) l * zmodWindow b L₂ l) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact sum_range_eq_inv_mul_dft_window _ b L₂
    _ = (q : ℂ)⁻¹ * ∑ l : ZMod q,
          ∑ i ∈ Finset.range L₁,
            ZMod.dft (f (a + (i : ZMod q))) l * zmodWindow b L₂ l := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm (s := Finset.range L₁)
        (t := (Finset.univ : Finset (ZMod q)))]
    _ = (q : ℂ)⁻¹ * ∑ l : ZMod q,
          zmodWindow b L₂ l *
            (∑ i ∈ Finset.range L₁,
              ZMod.dft (f (a + (i : ZMod q))) l) := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (q : ℂ)⁻¹ * ∑ l : ZMod q,
          zmodWindow b L₂ l *
            ((q : ℂ)⁻¹ * ∑ k : ZMod q,
              ZMod.dft (fun x => ZMod.dft (f x) l) k * zmodWindow a L₁ k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _hl
      congr 1
      exact sum_range_eq_inv_mul_dft_window
        (fun x => ZMod.dft (f x) l) a L₁
    _ = _ := by
      simp_rw [← zmodFourier2_eq_iteratedDft]
      rw [mul_assoc]
      apply congrArg ((q : ℂ)⁻¹ * ·)
      calc
        (∑ l : ZMod q,
            zmodWindow b L₂ l * ((q : ℂ)⁻¹ *
              ∑ k : ZMod q, zmodFourier2 f k l * zmodWindow a L₁ k)) =
            ∑ l : ZMod q, (q : ℂ)⁻¹ *
              ∑ k : ZMod q,
                zmodFourier2 f k l * zmodWindow a L₁ k * zmodWindow b L₂ l := by
          apply Finset.sum_congr rfl
          intro l _hl
          calc
            _ = zmodWindow b L₂ l * ∑ k : ZMod q,
                (q : ℂ)⁻¹ * (zmodFourier2 f k l * zmodWindow a L₁ k) := by
              rw [Finset.mul_sum]
            _ = ∑ k : ZMod q, zmodWindow b L₂ l *
                ((q : ℂ)⁻¹ * (zmodFourier2 f k l * zmodWindow a L₁ k)) := by
              rw [Finset.mul_sum]
            _ = (q : ℂ)⁻¹ * ∑ k : ZMod q,
                zmodFourier2 f k l * zmodWindow a L₁ k * zmodWindow b L₂ l := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _hk
              ring
        _ = (q : ℂ)⁻¹ * ∑ l : ZMod q, ∑ k : ZMod q,
              zmodFourier2 f k l * zmodWindow a L₁ k * zmodWindow b L₂ l := by
          rw [Finset.mul_sum]

private theorem sum_zmod_eq_sum_range
    {q : ℕ} [NeZero q] {A : Type*} [AddCommMonoid A] (g : ZMod q → A) :
    (∑ k : ZMod q, g k) = ∑ k ∈ Finset.range q, g (k : ZMod q) := by
  classical
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _hk
    exact congrArg g (ZMod.natCast_zmod_val k).symm

/-- Fourier completion of a shifted literal rectangle.  The coefficient
hypotheses concern the actual double transform `zmodFourier2`; no abstract
Fourier transform or inverse identity is supplied by the caller. -/
theorem norm_sum_box_le_of_fourier2_bound
    {q : ℕ} [NeZero q]
    (f : ZMod q → ZMod q → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hzero : zmodFourier2 f 0 0 = 0)
    (hbound : ∀ k l : ZMod q, (k, l) ≠ (0, 0) →
      ‖zmodFourier2 f k l‖ ≤ C * (q : ℝ))
    (a b : ZMod q) (L₁ L₂ : ℕ) :
    ‖∑ i ∈ Finset.range L₁, ∑ j ∈ Finset.range L₂,
      f (a + (i : ZMod q)) (b + (j : ZMod q))‖ ≤
      C * ((q : ℝ) * (1 + Real.log q) ^ 2 +
        ((L₁ : ℝ) + (L₂ : ℝ)) * (1 + Real.log q)) := by
  classical
  have hqN : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  let H : ℝ := 1 + Real.log q
  let S₁ : ℝ := ∑ k ∈ Finset.Ico 1 q, ‖zmodWindow a L₁ (k : ZMod q)‖
  let S₂ : ℝ := ∑ l ∈ Finset.Ico 1 q, ‖zmodWindow b L₂ (l : ZMod q)‖
  have hS₁ : S₁ ≤ (q : ℝ) * H := by
    simpa only [S₁, H, zmodWindow] using
      sum_norm_stdAddChar_sum_range_le a L₁
  have hS₂ : S₂ ≤ (q : ℝ) * H := by
    simpa only [S₂, H, zmodWindow] using
      sum_norm_stdAddChar_sum_range_le b L₂
  have hcast_ne (k : ℕ) (hk : k ∈ Finset.Ico 1 q) : (k : ZMod q) ≠ 0 := by
    intro hk0
    have hdiv : q ∣ k := (ZMod.natCast_eq_zero_iff k q).mp hk0
    exact (Nat.not_le_of_lt (Finset.mem_Ico.mp hk).2)
      (Nat.le_of_dvd (Finset.mem_Ico.mp hk).1 hdiv)
  have hid := sum_box_fourier_identity f a b L₁ L₂
  rw [sum_zmod_eq_sum_range] at hid
  simp_rw [sum_zmod_eq_sum_range] at hid
  rw [Finset.sum_range_eq_add_Ico _ hqN] at hid
  simp_rw [Finset.sum_range_eq_add_Ico _ hqN] at hid
  have hid' :
      (∑ i ∈ Finset.range L₁, ∑ j ∈ Finset.range L₂,
          f (a + (i : ZMod q)) (b + (j : ZMod q))) =
        (q : ℂ)⁻¹ * (q : ℂ)⁻¹ *
          ((∑ k ∈ Finset.Ico 1 q,
              zmodFourier2 f (k : ZMod q) 0 * zmodWindow a L₁ (k : ZMod q) * L₂) +
            ((∑ l ∈ Finset.Ico 1 q,
                zmodFourier2 f 0 (l : ZMod q) * L₁ * zmodWindow b L₂ (l : ZMod q)) +
              ∑ l ∈ Finset.Ico 1 q, ∑ k ∈ Finset.Ico 1 q,
                zmodFourier2 f (k : ZMod q) (l : ZMod q) *
                  zmodWindow a L₁ (k : ZMod q) * zmodWindow b L₂ (l : ZMod q))) := by
    rw [← Finset.sum_add_distrib]
    simpa only [Nat.cast_zero, hzero, zmodWindow_zero, zero_mul, zero_add,
      Nat.cast_ofNat] using hid
  have haxis₁ :
      ‖∑ k ∈ Finset.Ico 1 q,
          zmodFourier2 f (k : ZMod q) 0 * zmodWindow a L₁ (k : ZMod q) * L₂‖ ≤
        C * (q : ℝ) * (L₂ : ℝ) * S₁ := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 q,
          ‖zmodFourier2 f (k : ZMod q) 0 * zmodWindow a L₁ (k : ZMod q) * L₂‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico 1 q,
          (C * (q : ℝ)) * ‖zmodWindow a L₁ (k : ZMod q)‖ * (L₂ : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (hbound (k : ZMod q) 0 (by simp [hcast_ne k hk])) (norm_nonneg _))
          (Nat.cast_nonneg L₂)
      _ = C * (q : ℝ) * (L₂ : ℝ) * S₁ := by
        change _ = C * (q : ℝ) * (L₂ : ℝ) *
          (∑ k ∈ Finset.Ico 1 q, ‖zmodWindow a L₁ (k : ZMod q)‖)
        calc
          _ = (∑ k ∈ Finset.Ico 1 q,
              C * (q : ℝ) * ‖zmodWindow a L₁ (k : ZMod q)‖) * L₂ := by
            rw [Finset.sum_mul]
          _ = (C * (q : ℝ) *
              ∑ k ∈ Finset.Ico 1 q, ‖zmodWindow a L₁ (k : ZMod q)‖) * L₂ := by
            rw [Finset.mul_sum]
          _ = _ := by ring
  have haxis₂ :
      ‖∑ l ∈ Finset.Ico 1 q,
          zmodFourier2 f 0 (l : ZMod q) * L₁ * zmodWindow b L₂ (l : ZMod q)‖ ≤
        C * (q : ℝ) * (L₁ : ℝ) * S₂ := by
    calc
      _ ≤ ∑ l ∈ Finset.Ico 1 q,
          ‖zmodFourier2 f 0 (l : ZMod q) * L₁ * zmodWindow b L₂ (l : ZMod q)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Ico 1 q,
          (C * (q : ℝ)) * (L₁ : ℝ) * ‖zmodWindow b L₂ (l : ZMod q)‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (hbound 0 (l : ZMod q) (by simp [hcast_ne l hl])) (Nat.cast_nonneg L₁))
          (norm_nonneg _)
      _ = C * (q : ℝ) * (L₁ : ℝ) * S₂ := by
        change _ = C * (q : ℝ) * (L₁ : ℝ) *
          (∑ l ∈ Finset.Ico 1 q, ‖zmodWindow b L₂ (l : ZMod q)‖)
        rw [← Finset.mul_sum]
  have hinterior :
      ‖∑ l ∈ Finset.Ico 1 q, ∑ k ∈ Finset.Ico 1 q,
          zmodFourier2 f (k : ZMod q) (l : ZMod q) *
            zmodWindow a L₁ (k : ZMod q) * zmodWindow b L₂ (l : ZMod q)‖ ≤
        C * (q : ℝ) * S₁ * S₂ := by
    calc
      _ ≤ ∑ l ∈ Finset.Ico 1 q, ∑ k ∈ Finset.Ico 1 q,
          ‖zmodFourier2 f (k : ZMod q) (l : ZMod q) *
            zmodWindow a L₁ (k : ZMod q) * zmodWindow b L₂ (l : ZMod q)‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _l _hl => norm_sum_le _ _)
      _ ≤ ∑ l ∈ Finset.Ico 1 q, ∑ k ∈ Finset.Ico 1 q,
          (C * (q : ℝ)) * ‖zmodWindow a L₁ (k : ZMod q)‖ *
            ‖zmodWindow b L₂ (l : ZMod q)‖ := by
        apply Finset.sum_le_sum
        intro l hl
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (hbound (k : ZMod q) (l : ZMod q) (by simp [hcast_ne k hk]))
            (norm_nonneg _)) (norm_nonneg _)
      _ = C * (q : ℝ) * S₁ * S₂ := by
        change _ = C * (q : ℝ) *
          (∑ k ∈ Finset.Ico 1 q, ‖zmodWindow a L₁ (k : ZMod q)‖) *
          (∑ l ∈ Finset.Ico 1 q, ‖zmodWindow b L₂ (l : ZMod q)‖)
        calc
          _ = ∑ l ∈ Finset.Ico 1 q,
              (C * (q : ℝ) *
                (∑ k ∈ Finset.Ico 1 q, ‖zmodWindow a L₁ (k : ZMod q)‖)) *
                  ‖zmodWindow b L₂ (l : ZMod q)‖ := by
            apply Finset.sum_congr rfl
            intro l _hl
            rw [Finset.mul_sum, Finset.sum_mul]
          _ = _ := by rw [← Finset.mul_sum]
  rw [hid', norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  have hS₁nonneg : 0 ≤ S₁ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS₂nonneg : 0 ≤ S₂ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    (q : ℝ)⁻¹ * (q : ℝ)⁻¹ *
        ‖(∑ k ∈ Finset.Ico 1 q,
              zmodFourier2 f (k : ZMod q) 0 * zmodWindow a L₁ (k : ZMod q) * L₂) +
          ((∑ l ∈ Finset.Ico 1 q,
                zmodFourier2 f 0 (l : ZMod q) * L₁ * zmodWindow b L₂ (l : ZMod q)) +
            ∑ l ∈ Finset.Ico 1 q, ∑ k ∈ Finset.Ico 1 q,
              zmodFourier2 f (k : ZMod q) (l : ZMod q) *
                zmodWindow a L₁ (k : ZMod q) * zmodWindow b L₂ (l : ZMod q))‖ ≤
        (q : ℝ)⁻¹ * (q : ℝ)⁻¹ *
          (C * q * L₂ * S₁ + (C * q * L₁ * S₂ + C * q * S₁ * S₂)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (inv_nonneg.mpr hq.le) (inv_nonneg.mpr hq.le))
      exact (norm_add_le _ _).trans <| add_le_add haxis₁ <|
        (norm_add_le _ _).trans (add_le_add haxis₂ hinterior)
    _ ≤ (q : ℝ)⁻¹ * (q : ℝ)⁻¹ *
          (C * q * L₂ * (q * H) +
            (C * q * L₁ * (q * H) + C * q * (q * H) * (q * H))) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (inv_nonneg.mpr hq.le) (inv_nonneg.mpr hq.le))
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hS₁
          (mul_nonneg (mul_nonneg hC hq.le) (Nat.cast_nonneg L₂))
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hS₂
          (mul_nonneg (mul_nonneg hC hq.le) (Nat.cast_nonneg L₁))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hS₁ (mul_nonneg hC hq.le)) hS₂
        hS₂nonneg
        (mul_nonneg (mul_nonneg hC hq.le) (hS₁nonneg.trans hS₁))
    _ = C * ((q : ℝ) * H ^ 2 + ((L₁ : ℝ) + L₂) * H) := by
      field_simp
      ring

end

end PellPaper
