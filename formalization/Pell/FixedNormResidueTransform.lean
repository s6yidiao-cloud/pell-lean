import Mathlib.NumberTheory.Pell
import Mathlib.Data.Int.ModEq

/-!
# Direct Pell transport on a fixed nonzero norm level

Equal residue pairs modulo the nonzero level give an actual integral
norm-one Pell transform. The radicand and all coordinates may be arbitrary
integers. No positivity, squarefreeness, coprimality or ideal theory is used.
This is the arithmetic transport leaf, not an orbit or height count.
-/

namespace PellPaper

/-- Two integer solutions of `v*e^2-u*d^2=h` having the same two residues
modulo nonzero `h` are related by a literal norm-one Pell solution. -/
theorem exists_pell_transform_of_same_norm_modEq
    (u v h d e d' e' : ℤ) (hh : h ≠ 0)
    (hn : v * e ^ 2 - u * d ^ 2 = h)
    (hn' : v * e' ^ 2 - u * d' ^ 2 = h)
    (hd : d' ≡ d [ZMOD h]) (he : e' ≡ e [ZMOD h]) :
    ∃ q : Pell.Solution₁ (u * v),
      e' = q.x * e + u * q.y * d ∧
      d' = v * q.y * e + q.x * d := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hd.symm
  obtain ⟨l, hl⟩ := Int.modEq_iff_add_fac.mp he.symm
  let a := 1 + v * e * l - u * d * k
  let b := k * e - l * d
  have hA : v * e * e' - u * d * d' = h * a := by
    dsimp [a]
    rw [hk, hl]
    calc
      v * e * (e + h * l) - u * d * (d + h * k) =
          (v * e ^ 2 - u * d ^ 2) + h * (v * e * l - u * d * k) := by ring
      _ = h * (1 + v * e * l - u * d * k) := by rw [hn]; ring
  have hB : d' * e - e' * d = h * b := by
    dsimp [b]
    rw [hk, hl]
    ring
  have hnorm : a ^ 2 - (u * v) * b ^ 2 = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * (a ^ 2 - (u * v) * b ^ 2) =
          (h * a) ^ 2 - (u * v) * (h * b) ^ 2 := by ring
      _ = (v * e * e' - u * d * d') ^ 2 -
          (u * v) * (d' * e - e' * d) ^ 2 := by rw [hA, hB]
      _ = (v * e ^ 2 - u * d ^ 2) * (v * e' ^ 2 - u * d' ^ 2) := by ring
      _ = h ^ 2 * 1 := by rw [hn, hn']; ring
  refine ⟨Pell.Solution₁.mk a b hnorm, ?_, ?_⟩
  · change e' = a * e + u * b * d
    apply mul_left_cancel₀ hh
    calc
      h * e' = (v * e ^ 2 - u * d ^ 2) * e' := by rw [hn]
      _ = (v * e * e' - u * d * d') * e + u * (d' * e - e' * d) * d := by ring
      _ = h * (a * e + u * b * d) := by rw [hA, hB]; ring
  · change d' = v * b * e + a * d
    apply mul_left_cancel₀ hh
    calc
      h * d' = (v * e ^ 2 - u * d ^ 2) * d' := by rw [hn]
      _ = v * (d' * e - e' * d) * e + (v * e * e' - u * d * d') * d := by ring
      _ = h * (v * b * e + a * d) := by rw [hA, hB]; ring

/-- On a nonzero norm level, a Pell transform is uniquely determined by
the original vector and its image. No coordinate is individually nonzero
by assumption, and the norm-one equations are not needed for cancellation. -/
theorem pell_transform_unique_of_nonzero_norm
    (u v h d e : ℤ) (hh : h ≠ 0)
    (hn : v * e ^ 2 - u * d ^ 2 = h)
    (q r : Pell.Solution₁ (u * v))
    (he : q.x * e + u * q.y * d = r.x * e + u * r.y * d)
    (hd : v * q.y * e + q.x * d = v * r.y * e + r.x * d) : q = r := by
  have he0 : (q.x - r.x) * e + u * (q.y - r.y) * d = 0 := by linarith
  have hd0 : v * (q.y - r.y) * e + (q.x - r.x) * d = 0 := by linarith
  have hx : h * (q.x - r.x) = 0 := by
    calc
      h * (q.x - r.x) =
          v * e * ((q.x - r.x) * e + u * (q.y - r.y) * d) -
          u * d * (v * (q.y - r.y) * e + (q.x - r.x) * d) := by rw [← hn]; ring
      _ = 0 := by rw [he0, hd0]; ring
  have hy : h * (q.y - r.y) = 0 := by
    calc
      h * (q.y - r.y) =
          e * (v * (q.y - r.y) * e + (q.x - r.x) * d) -
          d * ((q.x - r.x) * e + u * (q.y - r.y) * d) := by rw [← hn]; ring
      _ = 0 := by rw [he0, hd0]; ring
  exact Pell.Solution₁.ext
    (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hh))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hh))

end PellPaper
