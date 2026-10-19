import Pell.AuxiliaryCurveDegenerateCounting

/-!
# Finite divisor gates for special auxiliary-parabola components

For a retained component of the form `a * (t - s^2) - b`, the exact Pell
equation gives `e^2 * u ∣ a * h`.  This file packages the resulting positive
denominator pairs as an explicit `Finset`, and injects that finset into data
consisting of a possible first denominator and a divisor of `|a h|`.

The bounds here are deliberately finite and elementary.  They do **not**
replace the divisor-function estimate needed to turn the manuscript's
`x^ε` factor into a uniform asymptotic bound.
-/

namespace PellPaper

noncomputable section

/-- Positive pairs `(e,u)` whose special-parabola denominator product
`e^2 * u` divides `N`.  When `N ≠ 0`, this is exactly the relevant finite
candidate set; the interval bounds are consequences of divisibility. -/
def specialParabolaDenominatorPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    fun p => p.1 ^ 2 * p.2 ∣ N

/-- Divisor data for `specialParabolaDenominatorPairs`: the first coordinate
is `e`, while the second is the product `e^2 * u`, recorded as a divisor of
`N`. -/
def specialParabolaDenominatorDivisorData (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product N.divisors).filter fun p => p.1 ^ 2 ∣ p.2

/-- Exact membership characterization of the positive denominator-pair gate.
The nonzero hypothesis is essential: every positive integer divides zero. -/
theorem mem_specialParabolaDenominatorPairs_iff
    {N e u : ℕ} (hN : N ≠ 0) :
    (e, u) ∈ specialParabolaDenominatorPairs N ↔
      0 < e ∧ 0 < u ∧ e ^ 2 * u ∣ N := by
  constructor
  · intro hmem
    rcases Finset.mem_filter.mp hmem with ⟨hbox, hdiv⟩
    rcases Finset.mem_product.mp hbox with ⟨he, hu⟩
    rw [Finset.mem_Icc] at he hu
    exact ⟨by omega, by omega, hdiv⟩
  · rintro ⟨he, hu, hdiv⟩
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hprodpos : 0 < e ^ 2 * u :=
      Nat.mul_pos (pow_pos he 2) hu
    have hprodle : e ^ 2 * u ≤ N := Nat.le_of_dvd hNpos hdiv
    have hele : e ≤ N := by
      calc
        e = e * 1 := (Nat.mul_one _).symm
        _ ≤ e * (e * u) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.mul_pos he hu))
        _ = e ^ 2 * u := by ring
        _ ≤ N := hprodle
    have hule : u ≤ N := by
      calc
        u = 1 * u := (Nat.one_mul _).symm
        _ ≤ e ^ 2 * u := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (pow_pos he 2))
        _ ≤ N := hprodle
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, hdiv⟩
    exact ⟨by simpa [Finset.mem_Icc] using ⟨he, hele⟩,
      by simpa [Finset.mem_Icc] using ⟨hu, hule⟩⟩

/-- The map retaining `e` and recording `e^2 u` sends every admissible
denominator pair into the corresponding divisor-data gate. -/
theorem specialParabolaDenominatorPairs_encode_mem_divisorData
    {N e u : ℕ} (hN : N ≠ 0)
    (hmem : (e, u) ∈ specialParabolaDenominatorPairs N) :
    (e, e ^ 2 * u) ∈ specialParabolaDenominatorDivisorData N := by
  rcases (mem_specialParabolaDenominatorPairs_iff hN).mp hmem with
    ⟨he, hu, hdiv⟩
  have heN : e ≤ N := by
    calc
      e = e * 1 := (Nat.mul_one _).symm
      _ ≤ e * (e * u) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.mul_pos he hu))
      _ = e ^ 2 * u := by ring
      _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdiv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ?_, ?_⟩
  · exact ⟨by simpa [Finset.mem_Icc] using
        ⟨Nat.succ_le_of_lt he, heN⟩,
      Nat.mem_divisors.mpr ⟨hdiv, hN⟩⟩
  · exact ⟨u, rfl⟩

/-- On the positive denominator-pair gate, `(e,u) ↦ (e,e^2u)` is injective.
Positivity of `e` is precisely what permits cancellation of `e^2`. -/
theorem specialParabolaDenominatorPairs_encode_injOn (N : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1, p.1 ^ 2 * p.2))
      (↑(specialParabolaDenominatorPairs N) : Set (ℕ × ℕ)) := by
  rintro ⟨e, u⟩ hmem ⟨e', u'⟩ hmem' hencode
  simp only [Prod.mk.injEq] at hencode
  rcases hencode with ⟨hee, hproduct⟩
  subst e'
  have he : 0 < e := by
    rcases Finset.mem_filter.mp hmem with ⟨hbox, _⟩
    have hIcc := (Finset.mem_product.mp hbox).1
    rw [Finset.mem_Icc] at hIcc
    omega
  have hsq : e ^ 2 ≠ 0 := (pow_pos he 2).ne'
  have huu : u = u' := by
    exact mul_left_cancel₀ hsq hproduct
  exact Prod.ext rfl huu

/-- The special-parabola denominator-pair gate has no more elements than its
explicit divisor-data gate. -/
theorem card_specialParabolaDenominatorPairs_le_divisorData
    (N : ℕ) (hN : N ≠ 0) :
    (specialParabolaDenominatorPairs N).card ≤
      (specialParabolaDenominatorDivisorData N).card := by
  refine Finset.card_le_card_of_injOn
    (fun p : ℕ × ℕ => (p.1, p.1 ^ 2 * p.2)) ?_
    (specialParabolaDenominatorPairs_encode_injOn N)
  intro p hp
  rcases p with ⟨e, u⟩
  exact specialParabolaDenominatorPairs_encode_mem_divisorData hN hp

/-- Elementary cardinality bound for the divisor-data gate.  The factor
`N.divisors.card` is intentionally retained for later insertion of a sharper
divisor estimate. -/
theorem card_specialParabolaDenominatorDivisorData_le
    (N : ℕ) :
    (specialParabolaDenominatorDivisorData N).card ≤
      N * N.divisors.card := by
  calc
    (specialParabolaDenominatorDivisorData N).card ≤
        ((Finset.Icc 1 N).product N.divisors).card :=
      Finset.card_filter_le _ _
    _ = N * N.divisors.card := by
      change (Finset.Icc 1 N ×ˢ N.divisors).card = N * N.divisors.card
      rw [Finset.card_product, Nat.card_Icc]
      simp

/-- Source-ready finite bound: positive denominator pairs with
`e^2 u ∣ N` number at most `N` times the number of divisors of `N`. -/
theorem card_specialParabolaDenominatorPairs_le_mul_card_divisors
    (N : ℕ) (hN : N ≠ 0) :
    (specialParabolaDenominatorPairs N).card ≤ N * N.divisors.card :=
  (card_specialParabolaDenominatorPairs_le_divisorData N hN).trans
    (card_specialParabolaDenominatorDivisorData_le N)

/-- A fully elementary fallback bound, obtained from `#divisors N ≤ N`.
The sharper preceding theorem is the useful interface for the manuscript's
eventual divisor-function input. -/
theorem card_specialParabolaDenominatorPairs_le_square
    (N : ℕ) (hN : N ≠ 0) :
    (specialParabolaDenominatorPairs N).card ≤ N ^ 2 := by
  calc
    (specialParabolaDenominatorPairs N).card ≤ N * N.divisors.card :=
      card_specialParabolaDenominatorPairs_le_mul_card_divisors N hN
    _ ≤ N * N := Nat.mul_le_mul_left _ (Nat.card_divisors_le_self N)
    _ = N ^ 2 := by ring

/-- A special auxiliary-parabola relation places its positive denominator
pair in the explicit finite divisor gate for `|a h|`. -/
theorem auxiliaryParabola_denominator_pair_mem_specialParabolaDenominatorPairs
    {a b h : ℤ} {d e u v : ℕ}
    (he : 0 < e) (hu : 0 < u)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h)
    (hprod : a * h ≠ 0) :
    (e, u) ∈ specialParabolaDenominatorPairs (a * h).natAbs := by
  apply (mem_specialParabolaDenominatorPairs_iff (Int.natAbs_ne_zero.mpr hprod)).mpr
  refine ⟨he, hu, ?_⟩
  rw [← Int.natCast_dvd]
  simpa using e_sq_mul_u_dvd_auxiliaryParabolaProduct haux hdiff

/-- If the special component has nonzero intercept, the bridge's exact
identity supplies the nonzero product required by the finite divisor gate. -/
theorem auxiliaryParabola_denominator_pair_mem_specialParabolaDenominatorPairs_of_intercept_ne_zero
    {a b h : ℤ} {d e u v : ℕ}
    (he : 0 < e) (hu : 0 < u) (hb : b ≠ 0)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (e, u) ∈ specialParabolaDenominatorPairs (a * h).natAbs := by
  apply auxiliaryParabola_denominator_pair_mem_specialParabolaDenominatorPairs
    he hu haux hdiff
  exact auxiliaryParabola_product_ne_zero_of_intercept_ne_zero he hu hb haux hdiff

/-- The retained special component has at most the explicit divisor-data
budget associated to `|a h|`; this is a finite arithmetic gate, not yet the
manuscript's `x^ε` divisor estimate. -/
theorem card_specialParabolaDenominatorPairs_of_auxiliary_product
    {a h : ℤ} (hprod : a * h ≠ 0) :
    (specialParabolaDenominatorPairs (a * h).natAbs).card ≤
      (a * h).natAbs * ((a * h).natAbs.divisors.card) := by
  exact card_specialParabolaDenominatorPairs_le_mul_card_divisors _
    (Int.natAbs_ne_zero.mpr hprod)

end

end PellPaper
