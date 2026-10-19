import Pell.SlopeLatticeFirstMinimum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Primitive attainment of the actual first slope minimum

Integer scaling of the literal slope sup norm is homogeneous. Dividing the
coordinate gcd of an actual minimizing nonzero integer vector therefore
forces that gcd to be one. The existing first minimum is attained by such
a primitive vector, and Mathlib completes it to a determinant-one matrix.
No reduced-coordinate width or coefficient-height bound is asserted here.
-/

namespace PellPaper

/-- Integer homogeneity of the literal slope norm, without restrictions on
the real parameters or the sign of the integer multiplier. -/
theorem slopeVectorSupNorm_zsmul (U V M z : ℝ) (k : ℤ) (v : ℤ × ℤ) :
    slopeVectorSupNorm U V M z (k • v) =
      |(k : ℝ)| * slopeVectorSupNorm U V M z v := by
  change max |M * ((k * v.1 : ℤ) : ℝ) / V - z * ((k * v.2 : ℤ) : ℝ) / U|
      |((k * v.2 : ℤ) : ℝ) / U| =
    |(k : ℝ)| * max |M * (v.1 : ℝ) / V - z * (v.2 : ℝ) / U| |(v.2 : ℝ) / U|
  simp only [Int.cast_mul]
  have hfirst : M * ((k : ℝ) * (v.1 : ℝ)) / V -
      z * ((k : ℝ) * (v.2 : ℝ)) / U =
      (k : ℝ) * (M * (v.1 : ℝ) / V - z * (v.2 : ℝ) / U) := by ring
  have hsecond : ((k : ℝ) * (v.2 : ℝ)) / U =
      (k : ℝ) * ((v.2 : ℝ) / U) := by ring
  rw [hfirst, hsecond, abs_mul, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg (k : ℝ))).symm

/-- Every globally minimizing nonzero integer vector is primitive.
Being merely below the determinant-scale upper bound would not suffice. -/
theorem isCoprime_of_slopeVectorSupNorm_minimal
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M)
    (v : ℤ × ℤ) (hv : v ≠ 0)
    (hmin : ∀ w : ℤ × ℤ, w ≠ 0 →
      slopeVectorSupNorm U V M z v ≤ slopeVectorSupNorm U V M z w) :
    IsCoprime v.1 v.2 := by
  have hgpos : 0 < Int.gcd v.1 v.2 := by
    apply Nat.pos_of_ne_zero
    intro hg
    obtain ⟨ha, hb⟩ := Int.gcd_eq_zero_iff.mp hg
    exact hv (Prod.ext ha hb)
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hgpos
  have hwne : (a, b) ≠ (0 : ℤ × ℤ) := by
    intro hw
    have ha0 : a = 0 := congrArg Prod.fst hw
    have hb0 : b = 0 := congrArg Prod.snd hw
    exact Nat.zero_ne_one
      (by simpa only [ha0, hb0, Int.gcd_zero_left, Int.natAbs_zero] using hab)
  have hdecomp : v = (Int.gcd v.1 v.2 : ℤ) • (a, b) := by
    apply Prod.ext
    · change v.1 = (Int.gcd v.1 v.2 : ℤ) * a
      simpa only [mul_comm] using ha
    · change v.2 = (Int.gcd v.1 v.2 : ℤ) * b
      simpa only [mul_comm] using hb
  have hscale : slopeVectorSupNorm U V M z v =
      (Int.gcd v.1 v.2 : ℝ) * slopeVectorSupNorm U V M z (a, b) := by
    calc
      slopeVectorSupNorm U V M z v =
          slopeVectorSupNorm U V M z ((Int.gcd v.1 v.2 : ℤ) • (a, b)) :=
        congrArg (slopeVectorSupNorm U V M z) hdecomp
      _ = (Int.gcd v.1 v.2 : ℝ) * slopeVectorSupNorm U V M z (a, b) := by
        have hgR : 0 ≤ (Int.gcd v.1 v.2 : ℝ) := Nat.cast_nonneg _
        simpa only [Int.cast_natCast, abs_of_nonneg hgR] using
          slopeVectorSupNorm_zsmul U V M z (Int.gcd v.1 v.2 : ℤ) (a, b)
  have hwpos := slopeVectorSupNorm_pos U V M z hU hV hM (a, b) hwne
  have hsmall := hmin (a, b) hwne
  have hgle : (Int.gcd v.1 v.2 : ℝ) ≤ 1 := by nlinarith
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  exact Nat.le_antisymm (by exact_mod_cast hgle) hgpos

/-- The actual first slope minimum has a primitive nonzero integer witness. -/
theorem exists_primitive_slopeVector_attaining_firstSupNorm
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ IsCoprime v.1 v.2 ∧
      slopeVectorSupNorm U V M z v = firstSlopeSupNorm U V M z := by
  obtain ⟨v, hv, heq⟩ :=
    exists_nonzero_slopeVector_attaining_firstSupNorm U V M z hU hV hM
  refine ⟨v, hv, ?_, heq⟩
  apply isCoprime_of_slopeVectorSupNorm_minimal U V M z hU hV hM v hv
  intro w hw
  rw [heq]
  exact firstSlopeSupNorm_le U V M z hU hV hM w hw

/-- Mathlib's determinant-one completion can have an actual first-minimum
vector as its first column. No control of the second column is claimed. -/
theorem exists_SL2_firstSlopeSupNorm
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      slopeVectorSupNorm U V M z (g 0 0, g 1 0) = firstSlopeSupNorm U V M z := by
  obtain ⟨v, _, hcop, heq⟩ :=
    exists_primitive_slopeVector_attaining_firstSupNorm U V M z hU hV hM
  obtain ⟨g, hfirst, hsecond⟩ := hcop.exists_SL2_col 0
  exact ⟨g, by simpa only [hfirst, hsecond, Prod.mk.eta] using heq⟩

end PellPaper
