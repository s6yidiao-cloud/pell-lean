import Pell.RawTargetSlopeRecovery
import Pell.DyadicSignedNormAggregation
import Pell.PrimitiveBinaryZeroCount

/-!
# Actual dyadic source counts on raw target zeros

The counted objects remain natural tuples `(d,e,u,v)`. Positive coprime raw
targets `(v,u)` of the same rational slope coincide, and projection to the
literal source pair `(d,e)` is injective on each such fibre. The proved
four-level fixed-parameter count gives at most `96*Q` points per slope.
A nonzero homogeneous binary target polynomial of degree `delta` has at
most `delta` slopes, giving an actual source count `96*Q*delta`.

This handles the raw-coordinate source-independent zero branch. It does
not count the residual eliminant squares, sum cells or construct a reduced
basis coordinate map. The scale is the literal dyadic `E^2*V` throughout.
-/

namespace PellPaper

/-- Every raw target slope in a literal dyadic factor family has at most
`96*Q` actual source tuples, including all four signed norm levels. -/
theorem card_dyadic_raw_target_slope_fibre_le_ninetySix_mul_Q
    (θ Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ q ∈ S, DyadicFactorCondition θ Y q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hbox : ∀ q ∈ S, q ∈ dyadicBox i) (r : Option ℚ) :
    ((S.filter fun q =>
      integralBinarySlope ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] = r).card : ℝ) ≤
        96 * Q := by
  classical
  let F := S.filter fun q =>
    integralBinarySlope ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] = r
  have hupos : ∀ q ∈ S, 0 < q.2.2.1 := fun q hq => (hcond q hq).2.2.1
  have hcop : ∀ q ∈ S, q.2.2.1.Coprime q.2.2.2 := by
    intro q hq
    rcases hcond q hq with ⟨_, _, _, _, _, _, _, _, _, _, hc, _⟩
    exact hc
  obtain ⟨hfixed, hproj⟩ :=
    fixed_raw_target_and_sourcePair_injective_on_slope S hupos hcop r
  change (F.card : ℝ) ≤ 96 * Q
  rcases F.eq_empty_or_nonempty with hF | ⟨p, hp⟩
  · simp only [hF, Finset.card_empty, Nat.cast_zero]
    linarith
  let P := F.image fun q => (q.1, q.2.1)
  have hPcard : P.card = F.card := Finset.card_image_of_injOn hproj
  have hPcond : ∀ w ∈ P,
      DyadicFactorCondition θ Y w.1 w.2 p.2.2.1 p.2.2.2 := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hu, hv⟩ := hfixed p hp q hq
    rw [hu, hv]
    exact hcond q (Finset.mem_filter.mp hq).1
  have hPbox : ∀ w ∈ P, (w.1, w.2, p.2.2.1, p.2.2.2) ∈ dyadicBox i := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hu, hv⟩ := hfixed p hp q hq
    rw [hu, hv]
    exact hbox q (Finset.mem_filter.mp hq).1
  have hc := card_dyadic_fixedParameter_pairs_le_ninetySix_mul_Q
    θ Q Y p.2.2.1 p.2.2.2 i hY hQ hxQ P hPcond hPbox
  simpa only [hPcard] using hc

/-- A finite literal dyadic tuple family whose raw targets all vanish on
a nonzero homogeneous degree-delta polynomial has at most `96*Q*delta`
members. No target fibre budget or source primitivity is assumed. -/
theorem card_dyadic_raw_target_zeros_le_ninetySix_mul_Q_mul_degree
    (θ Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (D : MvPolynomial (Fin 2) ℤ) (δ : ℕ)
    (hD : D.IsHomogeneous δ) (hD0 : D ≠ 0)
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ q ∈ S, DyadicFactorCondition θ Y q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hbox : ∀ q ∈ S, q ∈ dyadicBox i)
    (hzero : ∀ q ∈ S, MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0) :
    (S.card : ℝ) ≤ 96 * Q * (δ : ℝ) := by
  classical
  let t : (ℕ × ℕ × ℕ × ℕ) → (Fin 2 → ℤ) :=
    fun q => ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)]
  let k := fun q => integralBinarySlope (t q)
  have htarget : ∀ y ∈ S.image t,
      IsCoprime (y 0) (y 1) ∧ MvPolynomial.eval y D = 0 := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    rcases hcond q hq with ⟨_, _, _, _, _, _, _, _, _, _, hc, _⟩
    exact ⟨hc.symm.isCoprime, hzero q hq⟩
  have hkeys : (S.image k).card ≤ δ := by
    simpa only [Finset.image_image, k, Function.comp_def] using
      card_slopes_of_homogeneous_binary_zeros_le D δ hD hD0 (S.image t) htarget
  have hcard : (S.card : ℝ) = ∑ r ∈ S.image k,
      ((S.filter fun q => k q = r).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image k S
  calc
    (S.card : ℝ) = ∑ r ∈ S.image k, ((S.filter fun q => k q = r).card : ℝ) := hcard
    _ ≤ ∑ _ ∈ S.image k, 96 * Q := by
      apply Finset.sum_le_sum
      intro r _
      exact card_dyadic_raw_target_slope_fibre_le_ninetySix_mul_Q
        θ Q Y i hY hQ hxQ S hcond hbox r
    _ = ((S.image k).card : ℝ) * (96 * Q) := by simp
    _ ≤ (δ : ℝ) * (96 * Q) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hkeys) (by linarith)
    _ = 96 * Q * (δ : ℝ) := by ring

/-- The same actual source count for the retained raw target-zero filter
of an ambient dyadic family. Nonzero values in the ambient set are retained
outside this branch rather than assumed away. -/
theorem card_filter_dyadic_raw_target_zeros_le_ninetySix_mul_Q_mul_degree
    (θ Q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (D : MvPolynomial (Fin 2) ℤ) (δ : ℕ)
    (hD : D.IsHomogeneous δ) (hD0 : D ≠ 0)
    (S : Finset (ℕ × ℕ × ℕ × ℕ))
    (hcond : ∀ q ∈ S, DyadicFactorCondition θ Y q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hbox : ∀ q ∈ S, q ∈ dyadicBox i) :
    ((S.filter fun q =>
      MvPolynomial.eval ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] D = 0).card : ℝ) ≤
        96 * Q * (δ : ℝ) := by
  classical
  apply card_dyadic_raw_target_zeros_le_ninetySix_mul_Q_mul_degree θ Q Y i hY hQ hxQ D δ hD hD0
  · intro q hq
    exact hcond q (Finset.mem_filter.mp hq).1
  · intro q hq
    exact hbox q (Finset.mem_filter.mp hq).1
  · intro q hq
    exact (Finset.mem_filter.mp hq).2

end PellPaper
