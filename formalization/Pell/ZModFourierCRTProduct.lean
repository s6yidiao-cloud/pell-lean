import Pell.ZModFourierRectangle

/-!
# Chinese-remainder factorization of the double Fourier transform

For coprime nonzero moduli `m` and `n`, the standard additive character
modulo `m * n` is the product of the two local standard characters only
after multiplying the first CRT frequency by `n⁻¹` modulo `m` and the
second by `m⁻¹` modulo `n`.  This module records those literal transports
and proves that the actual unnormalised double Fourier transform of a CRT
product factors into its two local transforms.

No character compatibility or Fourier factorization is assumed from the
caller.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The first local frequency of a frequency modulo `m * n`.  The inverse
of the other modulus is required by the standard additive-character
normalisation. -/
def zmodCRTFirstFrequency {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (k : ZMod (m * n)) : ZMod m :=
  (n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) k).1

/-- The second local frequency of a frequency modulo `m * n`.  The inverse
of the other modulus is required by the standard additive-character
normalisation. -/
def zmodCRTSecondFrequency {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (k : ZMod (m * n)) : ZMod n :=
  (m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) k).2

/-- The product of two bivariate functions, transported to `ZMod (m * n)`
in both variables by the actual Chinese-remainder equivalence. -/
def zmodCRTProduct {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n)
    (f : ZMod m → ZMod m → ℂ) (g : ZMod n → ZMod n → ℂ) :
    ZMod (m * n) → ZMod (m * n) → ℂ := fun x y =>
  f ((ZMod.chineseRemainder h x).1) ((ZMod.chineseRemainder h y).1) *
    g ((ZMod.chineseRemainder h x).2) ((ZMod.chineseRemainder h y).2)

private theorem stdAddChar_crt_scaled
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (u : ZMod m) (v : ZMod n) :
    ZMod.stdAddChar
        ((ZMod.chineseRemainder h).symm
          ((n : ZMod m) * u, (m : ZMod n) * v)) =
      ZMod.stdAddChar u * ZMod.stdAddChar v := by
  let e := ZMod.chineseRemainder h
  have hrepr :
      e.symm ((n : ZMod m) * u, (m : ZMod n) * v) =
        ((n * u.val + m * v.val : ℕ) : ZMod (m * n)) := by
    apply e.injective
    rw [e.apply_symm_apply, map_natCast]
    ext <;> simp
  have hu : ZMod.stdAddChar u =
      Complex.exp (2 * Real.pi * Complex.I * (u.val : ℤ) / m) := by
    calc
      _ = ZMod.stdAddChar (u.val : ZMod m) :=
        congrArg ZMod.stdAddChar (ZMod.natCast_zmod_val u).symm
      _ = ZMod.stdAddChar ((u.val : ℤ) : ZMod m) := by norm_num
      _ = _ := ZMod.stdAddChar_coe (u.val : ℤ)
  have hv : ZMod.stdAddChar v =
      Complex.exp (2 * Real.pi * Complex.I * (v.val : ℤ) / n) := by
    calc
      _ = ZMod.stdAddChar (v.val : ZMod n) :=
        congrArg ZMod.stdAddChar (ZMod.natCast_zmod_val v).symm
      _ = ZMod.stdAddChar ((v.val : ℤ) : ZMod n) := by norm_num
      _ = _ := ZMod.stdAddChar_coe (v.val : ℤ)
  rw [hrepr, hu, hv]
  calc
    ZMod.stdAddChar ((n * u.val + m * v.val : ℕ) : ZMod (m * n)) =
        ZMod.stdAddChar
          (((n * u.val + m * v.val : ℕ) : ℤ) : ZMod (m * n)) := by norm_num
    _ = Complex.exp
        (2 * Real.pi * Complex.I * ((n * u.val + m * v.val : ℕ) : ℤ) / (m * n)) :=
      by simpa only [Nat.cast_mul] using
        (ZMod.stdAddChar_coe
          (N := m * n) ((n * u.val + m * v.val : ℕ) : ℤ))
    _ = Complex.exp (2 * Real.pi * Complex.I * (u.val : ℤ) / m) *
        Complex.exp (2 * Real.pi * Complex.I * (v.val : ℤ) / n) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
      have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      field_simp [hm, hn]

private theorem stdAddChar_chineseRemainder
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (t : ZMod (m * n)) :
    ZMod.stdAddChar t =
      ZMod.stdAddChar (zmodCRTFirstFrequency h t) *
        ZMod.stdAddChar (zmodCRTSecondFrequency h t) := by
  let e := ZMod.chineseRemainder h
  have ht : t = e.symm
      ((n : ZMod m) * zmodCRTFirstFrequency h t,
        (m : ZMod n) * zmodCRTSecondFrequency h t) := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext
    · simp only [e, zmodCRTFirstFrequency]
      rw [← mul_assoc, ZMod.coe_mul_inv_eq_one n h.symm, one_mul]
    · simp only [e, zmodCRTSecondFrequency]
      rw [← mul_assoc, ZMod.coe_mul_inv_eq_one m h, one_mul]
  calc
    ZMod.stdAddChar t = ZMod.stdAddChar
        (e.symm ((n : ZMod m) * zmodCRTFirstFrequency h t,
          (m : ZMod n) * zmodCRTSecondFrequency h t)) := congrArg _ ht
    _ = _ := stdAddChar_crt_scaled h _ _

private theorem stdAddChar_fourier_chineseRemainder
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (k l x y : ZMod (m * n)) :
    ZMod.stdAddChar (-k * x - l * y) =
      ZMod.stdAddChar
          (-zmodCRTFirstFrequency h k * (ZMod.chineseRemainder h x).1 -
            zmodCRTFirstFrequency h l * (ZMod.chineseRemainder h y).1) *
        ZMod.stdAddChar
          (-zmodCRTSecondFrequency h k * (ZMod.chineseRemainder h x).2 -
            zmodCRTSecondFrequency h l * (ZMod.chineseRemainder h y).2) := by
  rw [stdAddChar_chineseRemainder h]
  congr 1
  · apply congrArg ZMod.stdAddChar
    simp [zmodCRTFirstFrequency]
    ring
  · apply congrArg ZMod.stdAddChar
    simp [zmodCRTSecondFrequency]
    ring

/-- The literal negative, unnormalised double Fourier transform of a CRT
product is the product of the two local transforms at the rescaled local
frequencies. -/
theorem zmodFourier2_crtProduct
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n)
    (f : ZMod m → ZMod m → ℂ) (g : ZMod n → ZMod n → ℂ)
    (k l : ZMod (m * n)) :
    zmodFourier2 (zmodCRTProduct h f g) k l =
      zmodFourier2 f (zmodCRTFirstFrequency h k)
          (zmodCRTFirstFrequency h l) *
        zmodFourier2 g (zmodCRTSecondFrequency h k)
          (zmodCRTSecondFrequency h l) := by
  classical
  let e := ZMod.chineseRemainder h
  let k₁ := zmodCRTFirstFrequency h k
  let l₁ := zmodCRTFirstFrequency h l
  let k₂ := zmodCRTSecondFrequency h k
  let l₂ := zmodCRTSecondFrequency h l
  calc
    zmodFourier2 (zmodCRTProduct h f g) k l =
        ∑ X : ZMod m × ZMod n, ∑ Y : ZMod m × ZMod n,
          (f X.1 Y.1 * ZMod.stdAddChar (-k₁ * X.1 - l₁ * Y.1)) *
            (g X.2 Y.2 * ZMod.stdAddChar (-k₂ * X.2 - l₂ * Y.2)) := by
      rw [zmodFourier2]
      rw [← e.symm.sum_comp]
      apply Fintype.sum_congr
      intro X
      rw [← e.symm.sum_comp]
      apply Fintype.sum_congr
      intro Y
      simp only [zmodCRTProduct]
      rw [stdAddChar_fourier_chineseRemainder h]
      simp [e, k₁, l₁, k₂, l₂]
      ring
    _ = (∑ x : ZMod m, ∑ y : ZMod m,
          f x y * ZMod.stdAddChar (-k₁ * x - l₁ * y)) *
        (∑ x : ZMod n, ∑ y : ZMod n,
          g x y * ZMod.stdAddChar (-k₂ * x - l₂ * y)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Fintype.sum_mul_sum]
      simp_rw [Fintype.sum_mul_sum]
    _ = _ := by
      simp only [zmodFourier2, k₁, l₁, k₂, l₂]

/-- A global frequency is zero exactly when both rescaled CRT frequencies
are zero. -/
theorem zmodCRT_frequencies_eq_zero_iff
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (k : ZMod (m * n)) :
    (zmodCRTFirstFrequency h k = 0 ∧
      zmodCRTSecondFrequency h k = 0) ↔ k = 0 := by
  let e := ZMod.chineseRemainder h
  constructor
  · rintro ⟨hk₁, hk₂⟩
    have hfirst : (e k).1 = 0 := by
      have hmul := congrArg (fun z : ZMod m => (n : ZMod m) * z) hk₁
      simpa only [zmodCRTFirstFrequency, e, ← mul_assoc,
        ZMod.coe_mul_inv_eq_one n h.symm, one_mul, mul_zero] using hmul
    have hsecond : (e k).2 = 0 := by
      have hmul := congrArg (fun z : ZMod n => (m : ZMod n) * z) hk₂
      simpa only [zmodCRTSecondFrequency, e, ← mul_assoc,
        ZMod.coe_mul_inv_eq_one m h, one_mul, mul_zero] using hmul
    apply e.injective
    rw [map_zero]
    exact Prod.ext hfirst hsecond
  · rintro rfl
    simp [zmodCRTFirstFrequency, zmodCRTSecondFrequency]

/-- A nonzero global pair of Fourier frequencies gives a nonzero local pair
at at least one of the two coprime factors. -/
theorem zmodCRT_frequencyPairs_ne_zero_iff
    {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (k l : ZMod (m * n)) :
    (k, l) ≠ (0, 0) ↔
      (zmodCRTFirstFrequency h k, zmodCRTFirstFrequency h l) ≠ (0, 0) ∨
        (zmodCRTSecondFrequency h k, zmodCRTSecondFrequency h l) ≠ (0, 0) := by
  constructor
  · intro hkl
    by_contra hlocal
    simp only [not_or, not_ne_iff] at hlocal
    have hk : k = 0 := (zmodCRT_frequencies_eq_zero_iff h k).mp
      ⟨congrArg Prod.fst hlocal.1, congrArg Prod.fst hlocal.2⟩
    have hl : l = 0 := (zmodCRT_frequencies_eq_zero_iff h l).mp
      ⟨congrArg Prod.snd hlocal.1, congrArg Prod.snd hlocal.2⟩
    exact hkl (Prod.ext hk hl)
  · intro hlocal hkl
    have hk : k = 0 := congrArg Prod.fst hkl
    have hl : l = 0 := congrArg Prod.snd hkl
    subst k
    subst l
    simp [zmodCRTFirstFrequency, zmodCRTSecondFrequency] at hlocal

end

end PellPaper
