import Pell.ShiftedSquareCongruenceWindowAverage
import Pell.DivisorSummatoryLogBound
import Pell.QuadraticCongruenceRootCount
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.QuotientRing

/-!
# Proof of the shifted-square congruence-window average

This isolated module develops the two missing elementary ingredients: a
uniform root bound for the congruence modulo `d ^ 2`, and a logarithmic
average for the divisor-counting majorant.
-/

namespace PellPaper

noncomputable section

/-- Residues modulo `d ^ 2` which solve the shifted-square congruence. -/
noncomputable def shiftedSquareResidueRoots
    (a : ℤ) (d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (d ^ 2)).filter fun r ↦
    (d : ℤ) ^ 2 ∣ (r : ℤ) ^ 2 + a

@[simp] theorem mem_shiftedSquareResidueRoots
    {a : ℤ} {d r : ℕ} :
    r ∈ shiftedSquareResidueRoots a d ↔
      r < d ^ 2 ∧ (d : ℤ) ^ 2 ∣ (r : ℤ) ^ 2 + a := by
  classical
  simp [shiftedSquareResidueRoots]

/-- A nonempty shifted-square congruence forces the shift to be coprime to
the denominator.  Squarefreeness is used exactly here: a common prime would
force its square to divide the shift. -/
theorem natAbs_coprime_of_shiftedSquare_root
    {a : ℤ} {d r : ℕ} (ha : Squarefree a)
    (hroot : (d : ℤ) ^ 2 ∣ (r : ℤ) ^ 2 + a) :
    a.natAbs.Coprime d := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpd
  have hpZd : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
  have hp2sum : (p : ℤ) ^ 2 ∣ (r : ℤ) ^ 2 + a :=
    (pow_dvd_pow_of_dvd hpZd 2).trans hroot
  have hpaZ : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hpa
  have hpsum : (p : ℤ) ∣ (r : ℤ) ^ 2 + a :=
    (dvd_pow_self (p : ℤ) (by norm_num : (2 : ℕ) ≠ 0)).trans hp2sum
  have hprsq : (p : ℤ) ∣ (r : ℤ) ^ 2 := by
    simpa using dvd_sub hpsum hpaZ
  have hpr : p ∣ r := by
    apply hp.dvd_of_dvd_pow
    simpa only [Int.natCast_dvd, Int.natAbs_pow, Int.natAbs_natCast] using hprsq
  have hp2r : (p : ℤ) ^ 2 ∣ (r : ℤ) ^ 2 :=
    pow_dvd_pow_of_dvd (by exact_mod_cast hpr) 2
  have hp2aZ : (p : ℤ) ^ 2 ∣ a := by
    have h := dvd_sub hp2sum hp2r
    simpa only [add_sub_cancel_left] using h
  have hp2a : p ^ 2 ∣ a.natAbs := by
    rw [← Int.natCast_dvd]
    simpa using hp2aZ
  have haNat : Squarefree a.natAbs := Int.squarefree_natAbs.mpr ha
  exact (Nat.squarefree_iff_prime_squarefree.mp haNat p hp)
    (by simpa [pow_two] using hp2a)

private theorem zmod_sq_eq_neg_of_shiftedSquare_dvd
    {a : ℤ} {d r : ℕ}
    (hroot : (d : ℤ) ^ 2 ∣ (r : ℤ) ^ 2 + a) :
    (r : ZMod (d ^ 2)) ^ 2 = -(a : ZMod (d ^ 2)) := by
  have hzero :
      (((r : ℤ) ^ 2 + a : ℤ) : ZMod (d ^ 2)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [Nat.cast_pow] using hroot
  norm_num only [Int.cast_add, Int.cast_pow, Int.cast_natCast] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- The explicit residue finset injects into the corresponding ring-valued
square-root fibre. -/
theorem card_shiftedSquareResidueRoots_le_zmod_sq_fiber
    (a : ℤ) (d : ℕ) (hd : 0 < d) :
    (shiftedSquareResidueRoots a d).card ≤
      Nat.card {x : ZMod (d ^ 2) // x ^ 2 = -(a : ZMod (d ^ 2))} := by
  classical
  let _ : NeZero (d ^ 2) := ⟨pow_ne_zero 2 (Nat.ne_of_gt hd)⟩
  let liftRoot : {r : ℕ // r ∈ shiftedSquareResidueRoots a d} →
      {x : ZMod (d ^ 2) // x ^ 2 = -(a : ZMod (d ^ 2))} := fun r ↦
    ⟨(r.1 : ZMod (d ^ 2)),
      zmod_sq_eq_neg_of_shiftedSquare_dvd
        (mem_shiftedSquareResidueRoots.mp r.2).2⟩
  have hinj : Function.Injective liftRoot := by
    intro r s hrs
    apply Subtype.ext
    have hval := congrArg ZMod.val (congrArg Subtype.val hrs)
    simpa only [liftRoot,
      ZMod.val_natCast_of_lt (mem_shiftedSquareResidueRoots.mp r.2).1,
      ZMod.val_natCast_of_lt (mem_shiftedSquareResidueRoots.mp s.2).1] using hval
  calc
    (shiftedSquareResidueRoots a d).card =
        Nat.card {r : ℕ // r ∈ shiftedSquareResidueRoots a d} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card {x : ZMod (d ^ 2) //
        x ^ 2 = -(a : ZMod (d ^ 2))} :=
      Nat.card_le_card_of_injective liftRoot hinj

/-- Chinese remaindering injects a square-root fibre modulo `q` into the
product of its prime-power square-root fibres. -/
theorem natCard_zmod_sq_fiber_le_prod_primeFactors
    (q : ℕ) (hq : q ≠ 0) (c : ZMod q) :
    Nat.card {x : ZMod q // x ^ 2 = c} ≤
      ∏ p : q.primeFactors,
        Nat.card {y : ZMod (p.1 ^ q.factorization p.1) //
          y ^ 2 = ZMod.equivPi q hq c p} := by
  classical
  let e := ZMod.equivPi q hq
  let _ (p : q.primeFactors) : NeZero (p.1 ^ q.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.Prime.ne_zero (Nat.mem_primeFactors.mp p.2).1)⟩
  let toLocal : {x : ZMod q // x ^ 2 = c} →
      (∀ p : q.primeFactors,
        {y : ZMod (p.1 ^ q.factorization p.1) //
          y ^ 2 = ZMod.equivPi q hq c p}) := fun x p ↦ by
    refine ⟨ZMod.equivPi q hq x.1 p, ?_⟩
    change ((ZMod.equivPi q hq x.1) ^ 2) p = ZMod.equivPi q hq c p
    rw [← map_pow, x.2]
  have hinj : Function.Injective toLocal := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    funext p
    exact congr_arg (fun z ↦ z.1) (congr_fun hxy p)
  calc
    Nat.card {x : ZMod q // x ^ 2 = c} ≤
        Nat.card (∀ p : q.primeFactors,
          {y : ZMod (p.1 ^ q.factorization p.1) //
            y ^ 2 = ZMod.equivPi q hq c p}) :=
      Nat.card_le_card_of_injective toLocal hinj
    _ = ∏ p : q.primeFactors,
        Nat.card {y : ZMod (p.1 ^ q.factorization p.1) //
          y ^ 2 = ZMod.equivPi q hq c p} := Nat.card_pi

private theorem crtCoordinate_isUnit
    {q : ℕ} (hq : q ≠ 0) {c : ZMod q} (hc : IsUnit c)
    (p : q.primeFactors) :
    IsUnit (ZMod.equivPi q hq c p) := by
  exact ((hc.map (ZMod.equivPi q hq).toRingHom).map (Pi.evalRingHom _ p))

/-- A product with at most one exceptional factor of size four, and all
other factors of size two, has the expected binary bound. -/
theorem prod_subtype_le_two_mul_two_pow_card
    (s : Finset ℕ) (f : s → ℕ)
    (hodd : ∀ p : s, (p : ℕ) ≠ 2 → f p ≤ 2)
    (htwo : ∀ p : s, (p : ℕ) = 2 → f p ≤ 4) :
    (∏ p : s, f p) ≤ 2 * 2 ^ s.card := by
  classical
  calc
    (∏ p : s, f p) ≤ ∏ p : s, if (p : ℕ) = 2 then 4 else 2 := by
      apply Finset.prod_le_prod
      · simp
      · intro p _hp
        by_cases hp2 : (p : ℕ) = 2
        · simpa [hp2] using htwo p hp2
        · simpa [hp2] using hodd p hp2
    _ = ∏ p ∈ s, if p = 2 then 4 else 2 := by
      simpa only using
        (Finset.prod_coe_sort s (fun p : ℕ ↦ if p = 2 then 4 else 2))
    _ ≤ 2 * 2 ^ s.card := by
      by_cases h2 : 2 ∈ s
      · rw [← Finset.prod_erase_mul s
          (fun p : ℕ ↦ if p = 2 then 4 else 2) h2]
        simp only [if_pos]
        have herase :
            (∏ p ∈ s.erase 2, if p = 2 then 4 else 2) =
              ∏ _p ∈ s.erase 2, 2 := by
          apply Finset.prod_congr rfl
          intro p hp
          have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
          simp [hp2]
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
          (Finset.card_ne_zero.mpr ⟨2, h2⟩)
        have heraseCard : (s.erase 2).card = k := by
          rw [Finset.card_erase_of_mem h2, hk]
          omega
        rw [herase, Finset.prod_const, heraseCard, hk]
        simp only [Nat.succ_eq_add_one, pow_succ]
        ring_nf
        exact le_rfl
      · have hall : ∀ p ∈ s, p ≠ 2 := fun p hp hp2 ↦ h2 (hp2 ▸ hp)
        have hs :
            (∏ p ∈ s, if p = 2 then 4 else 2) = ∏ _p ∈ s, 2 := by
          apply Finset.prod_congr rfl
          intro p hp
          simp [hall p hp]
        rw [hs, Finset.prod_const]
        omega

/-- A unit modulo a nonzero natural number has at most two choices at each
odd prime and at most four choices at the unique possible two-primary
factor. -/
theorem natCard_zmod_sq_fiber_le_two_mul_two_pow_primeFactors
    {q : ℕ} (hq : q ≠ 0) {c : ZMod q} (hc : IsUnit c) :
    Nat.card {x : ZMod q // x ^ 2 = c} ≤
      2 * 2 ^ q.primeFactors.card := by
  calc
    Nat.card {x : ZMod q // x ^ 2 = c} ≤
        ∏ p : q.primeFactors,
          Nat.card {y : ZMod (p.1 ^ q.factorization p.1) //
            y ^ 2 = ZMod.equivPi q hq c p} :=
      natCard_zmod_sq_fiber_le_prod_primeFactors q hq c
    _ ≤ 2 * 2 ^ q.primeFactors.card := by
      apply prod_subtype_le_two_mul_two_pow_card
      · intro p hp2
        have hp : Nat.Prime p.1 := (Nat.mem_primeFactors.mp p.2).1
        exact natCard_zmod_oddPrimePow_ring_sq_fiber_le_two hp hp2
          (crtCoordinate_isUnit hq hc p)
      · rintro ⟨p, hpMem⟩ hp2
        dsimp only at hp2 ⊢
        subst p
        exact natCard_zmod_twoPow_ring_sq_fiber_le_four
          (crtCoordinate_isUnit hq hc ⟨2, hpMem⟩)

/-- The binary choice at every prime divisor is bounded by the full divisor
count. -/
theorem two_pow_card_primeFactors_le_card_divisors
    (d : ℕ) (hd : d ≠ 0) :
    2 ^ d.primeFactors.card ≤ d.divisors.card := by
  rw [Nat.card_divisors hd]
  calc
    2 ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ d.primeFactors, (d.factorization p + 1) := by
      gcongr with p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      have hfac : 0 < d.factorization p :=
        hpp.factorization_pos_of_dvd hd hpd
      omega

/-- The numerator fibre for one fixed denominator.  Its predicate is chosen
to match `shiftedSquareCongruencePairs` literally. -/
noncomputable def shiftedSquareCongruenceNumerators
    (a : ℤ) (d N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter fun n ↦
    0 < d ∧ 0 < n ∧ (d : ℤ) ^ 2 ∣ (n : ℤ) ^ 2 + a

@[simp] theorem mem_shiftedSquareCongruenceNumerators
    {a : ℤ} {d N n : ℕ} :
    n ∈ shiftedSquareCongruenceNumerators a d N ↔
      N ≤ n ∧ n < 2 * N ∧ 0 < d ∧ 0 < n ∧
        (d : ℤ) ^ 2 ∣ (n : ℤ) ^ 2 + a := by
  classical
  simp [shiftedSquareCongruenceNumerators, and_assoc]

private theorem mod_square_add_dvd_of_square_add_dvd
    {a : ℤ} {d n : ℕ}
    (hdiv : (d : ℤ) ^ 2 ∣ (n : ℤ) ^ 2 + a) :
    (d : ℤ) ^ 2 ∣ ((n % (d ^ 2) : ℕ) : ℤ) ^ 2 + a := by
  have hmodNat : n % (d ^ 2) ≡ n [MOD d ^ 2] := Nat.mod_modEq n (d ^ 2)
  have hmodInt :
      ((n % (d ^ 2) : ℕ) : ℤ) ≡ (n : ℤ) [ZMOD (d : ℤ) ^ 2] := by
    rw [show (d : ℤ) ^ 2 = ((d ^ 2 : ℕ) : ℤ) by norm_num]
    exact Int.natCast_modEq_iff.mpr hmodNat
  have hzero : (n : ℤ) ^ 2 + a ≡ 0 [ZMOD (d : ℤ) ^ 2] :=
    Int.modEq_zero_iff_dvd.mpr hdiv
  exact Int.modEq_zero_iff_dvd.mp <|
    ((hmodInt.pow 2).add (Int.ModEq.rfl : a ≡ a [ZMOD (d : ℤ) ^ 2])).trans hzero

/-- Quotient and residue give an injection of one numerator fibre into the
Cartesian product of residue roots and quotient blocks. -/
theorem card_shiftedSquareCongruenceNumerators_le
    (a : ℤ) (d N : ℕ) :
    (shiftedSquareCongruenceNumerators a d N).card ≤
      (shiftedSquareResidueRoots a d).card *
        (2 * N / (d ^ 2) + 1) := by
  classical
  let target := (shiftedSquareResidueRoots a d).product
    (Finset.range (2 * N / (d ^ 2) + 1))
  let code : ℕ → ℕ × ℕ := fun n ↦ (n % (d ^ 2), n / (d ^ 2))
  have hmem : ∀ n ∈ shiftedSquareCongruenceNumerators a d N,
      code n ∈ target := by
    intro n hn
    rw [mem_shiftedSquareCongruenceNumerators] at hn
    change (n % (d ^ 2), n / (d ^ 2)) ∈
      (shiftedSquareResidueRoots a d).product
        (Finset.range (2 * N / (d ^ 2) + 1))
    apply Finset.mk_mem_product
    · rw [mem_shiftedSquareResidueRoots]
      exact ⟨Nat.mod_lt _ (pow_pos hn.2.2.1 2),
        mod_square_add_dvd_of_square_add_dvd hn.2.2.2.2⟩
    · rw [Finset.mem_range]
      exact (Nat.div_le_div_right (Nat.le_of_lt hn.2.1)).trans_lt
        (Nat.lt_succ_self _)
  have hinj : Set.InjOn code
      {n : ℕ | n ∈ shiftedSquareCongruenceNumerators a d N} := by
    intro n hn m hm hcode
    simp only [code, Prod.mk.injEq] at hcode
    calc
      n = n % (d ^ 2) + (d ^ 2) * (n / (d ^ 2)) := (Nat.mod_add_div _ _).symm
      _ = m % (d ^ 2) + (d ^ 2) * (m / (d ^ 2)) := by rw [hcode.1, hcode.2]
      _ = m := Nat.mod_add_div _ _
  calc
    (shiftedSquareCongruenceNumerators a d N).card ≤ target.card := by
      exact Finset.card_le_card_of_injOn code hmem hinj
    _ = (shiftedSquareResidueRoots a d).card *
        (2 * N / (d ^ 2) + 1) := by
      simp [target]

/-- Exact decomposition of the pair count into fixed-denominator numerator
fibres. -/
theorem card_shiftedSquareCongruencePairs_eq_sum_numerators
    (a : ℤ) (D N : ℕ) :
    (shiftedSquareCongruencePairs a D N).card =
      ∑ d ∈ Finset.Ico D (2 * D),
        (shiftedSquareCongruenceNumerators a d N).card := by
  classical
  simp only [shiftedSquareCongruencePairs,
    shiftedSquareCongruenceNumerators, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  exact
    (Finset.sum_product (Finset.Ico D (2 * D)) (Finset.Ico N (2 * N))
      (fun p : ℕ × ℕ ↦
        if 0 < p.1 ∧ 0 < p.2 ∧
            (p.1 : ℤ) ^ 2 ∣ (p.2 : ℤ) ^ 2 + a then 1 else 0))

/-- The sole remaining arithmetic input after the fibre decomposition: for a
squarefree nonzero shift, the number of roots modulo `d ^ 2` is majorized by
four times the divisor function of `d`. -/
def ShiftedSquareResidueRootDivisorBound : Prop :=
  ∀ (a : ℤ) (d : ℕ), Squarefree a → a ≠ 0 → 0 < d →
    (shiftedSquareResidueRoots a d).card ≤ 4 * d.divisors.card

private theorem neg_intCast_isUnit_of_natAbs_coprime
    {a : ℤ} {q : ℕ} (haq : a.natAbs.Coprime q) :
    IsUnit (-(a : ZMod q)) := by
  have hu : IsUnit ((a.natAbs : ℕ) : ZMod q) :=
    (ZMod.isUnit_iff_coprime _ _).2 haq
  rcases Int.natAbs_eq a with ha | ha
  · rw [ha]
    simpa using hu.neg
  · rw [ha]
    simpa using hu

/-- The local residue-root divisor bound, obtained by CRT from the odd and
two-primary prime-power root bounds. -/
theorem shiftedSquareResidueRootDivisorBound_proved :
    ShiftedSquareResidueRootDivisorBound := by
  intro a d ha _ha0 hd
  by_cases hroots : (shiftedSquareResidueRoots a d).Nonempty
  · obtain ⟨r, hr⟩ := hroots
    have hcoprime : a.natAbs.Coprime d :=
      natAbs_coprime_of_shiftedSquare_root ha
        (mem_shiftedSquareResidueRoots.mp hr).2
    have hunit : IsUnit (-(a : ZMod (d ^ 2))) :=
      neg_intCast_isUnit_of_natAbs_coprime (hcoprime.pow_right 2)
    have hfiber :
        Nat.card {x : ZMod (d ^ 2) // x ^ 2 = -(a : ZMod (d ^ 2))} ≤
          2 * 2 ^ d.primeFactors.card := by
      simpa only [Nat.primeFactors_pow d (by norm_num : (2 : ℕ) ≠ 0)] using
        natCard_zmod_sq_fiber_le_two_mul_two_pow_primeFactors
          (pow_ne_zero 2 (Nat.ne_of_gt hd)) hunit
    calc
      (shiftedSquareResidueRoots a d).card ≤
          Nat.card {x : ZMod (d ^ 2) //
            x ^ 2 = -(a : ZMod (d ^ 2))} :=
        card_shiftedSquareResidueRoots_le_zmod_sq_fiber a d hd
      _ ≤ 2 * 2 ^ d.primeFactors.card := hfiber
      _ ≤ 2 * d.divisors.card :=
        Nat.mul_le_mul_left 2
          (two_pow_card_primeFactors_le_card_divisors d (Nat.ne_of_gt hd))
      _ ≤ 4 * d.divisors.card := by omega
  · have hempty : shiftedSquareResidueRoots a d = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hroots
    simp [hempty]

/-- Natural-number pair bound obtained from the residue-root divisor
majorant. -/
theorem card_shiftedSquareCongruencePairs_le_of_rootDivisorBound
    (hroot : ShiftedSquareResidueRootDivisorBound)
    (a : ℤ) (D N : ℕ) (ha : Squarefree a) (ha0 : a ≠ 0) (hD : 1 ≤ D) :
    (shiftedSquareCongruencePairs a D N).card ≤
      ∑ d ∈ Finset.Ico D (2 * D),
        4 * d.divisors.card * (2 * N / (d ^ 2) + 1) := by
  rw [card_shiftedSquareCongruencePairs_eq_sum_numerators]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := lt_of_lt_of_le (by omega : 0 < D) (Finset.mem_Ico.mp hd).1
  calc
    (shiftedSquareCongruenceNumerators a d N).card ≤
        (shiftedSquareResidueRoots a d).card *
          (2 * N / (d ^ 2) + 1) :=
      card_shiftedSquareCongruenceNumerators_le a d N
    _ ≤ (4 * d.divisors.card) * (2 * N / (d ^ 2) + 1) := by
      exact Nat.mul_le_mul_right _ (hroot a d ha ha0 hdpos)

private theorem cast_root_majorant_term_le
    {D d N : ℕ} (hD : 1 ≤ D) (hDd : D ≤ d) :
    ((4 * d.divisors.card * (2 * N / (d ^ 2) + 1) : ℕ) : ℝ) ≤
      4 * (d.divisors.card : ℝ) *
        (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le hDpos (by exact_mod_cast hDd)
  have hquot :
      ((2 * N / (d ^ 2) : ℕ) : ℝ) ≤
        2 * (N : ℝ) / (D : ℝ) ^ 2 := by
    calc
      ((2 * N / (d ^ 2) : ℕ) : ℝ) ≤
          ((2 * N : ℕ) : ℝ) / ((d ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = 2 * (N : ℝ) / (d : ℝ) ^ 2 := by norm_num
      _ ≤ 2 * (N : ℝ) / (D : ℝ) ^ 2 := by
        gcongr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  gcongr

private theorem sum_Ico_card_divisors_cast_le
    (D : ℕ) (_hD : 1 ≤ D) :
    ((∑ d ∈ Finset.Ico D (2 * D), d.divisors.card : ℕ) : ℝ) ≤
      (2 * D : ℝ) * (1 + Real.log (2 * D : ℕ)) := by
  have hsubset : Finset.Ico D (2 * D) ⊆ Finset.Ioc 0 (2 * D) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    rw [Finset.mem_Ioc]
    omega
  calc
    ((∑ d ∈ Finset.Ico D (2 * D), d.divisors.card : ℕ) : ℝ) ≤
        ((∑ d ∈ Finset.Ioc 0 (2 * D), d.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ (2 * D : ℝ) * (1 + Real.log (2 * D : ℕ)) :=
      by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          sum_Ioc_card_divisors_cast_le_mul_one_add_log (2 * D)

/-- Once the local root count is available, all interval and average-order
bookkeeping closes with one absolute real constant. -/
theorem shiftedSquareCongruencePairs_cast_le_of_rootDivisorBound
    (hroot : ShiftedSquareResidueRootDivisorBound)
    (a : ℤ) (D N : ℕ) (ha : Squarefree a) (ha0 : a ≠ 0)
    (hD : 1 ≤ D) :
    ((shiftedSquareCongruencePairs a D N).card : ℝ) ≤
      16 * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
        (1 + Real.log (2 * (D : ℝ)))) := by
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hnat :=
    card_shiftedSquareCongruencePairs_le_of_rootDivisorBound
      hroot a D N ha ha0 hD
  have hcast :
      ((shiftedSquareCongruencePairs a D N).card : ℝ) ≤
        ∑ d ∈ Finset.Ico D (2 * D),
          ((4 * d.divisors.card * (2 * N / (d ^ 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hdivsum :
      (∑ d ∈ Finset.Ico D (2 * D), (d.divisors.card : ℝ)) ≤
        (2 * (D : ℝ)) * (1 + Real.log (2 * (D : ℝ))) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using
      sum_Ico_card_divisors_cast_le D hD
  have hlog : 0 ≤ 1 + Real.log (2 * (D : ℝ)) := by
    have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have htwoD : (1 : ℝ) ≤ 2 * D := by nlinarith
    have := Real.log_nonneg htwoD
    linarith
  calc
    ((shiftedSquareCongruencePairs a D N).card : ℝ) ≤
        ∑ d ∈ Finset.Ico D (2 * D),
          ((4 * d.divisors.card * (2 * N / (d ^ 2) + 1) : ℕ) : ℝ) := hcast
    _ ≤ ∑ d ∈ Finset.Ico D (2 * D),
        4 * (d.divisors.card : ℝ) *
          (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      exact cast_root_majorant_term_le hD (Finset.mem_Ico.mp hd).1
    _ = 4 * (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) *
        (∑ d ∈ Finset.Ico D (2 * D), (d.divisors.card : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 4 * (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) *
        ((2 * (D : ℝ)) * (1 + Real.log (2 * (D : ℝ)))) := by
      gcongr
    _ ≤ 16 * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
        (1 + Real.log (2 * (D : ℝ)))) := by
      have hscale :
          4 * (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) *
              (2 * (D : ℝ)) ≤
            16 * ((N : ℝ) / (D : ℝ) + (D : ℝ)) := by
        field_simp
        nlinarith [sq_nonneg (D : ℝ)]
      calc
        4 * (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) *
            ((2 * (D : ℝ)) * (1 + Real.log (2 * (D : ℝ)))) =
          (4 * (2 * (N : ℝ) / (D : ℝ) ^ 2 + 1) *
            (2 * (D : ℝ))) * (1 + Real.log (2 * (D : ℝ))) := by ring
        _ ≤ (16 * ((N : ℝ) / (D : ℝ) + (D : ℝ))) *
            (1 + Real.log (2 * (D : ℝ))) :=
          mul_le_mul_of_nonneg_right hscale hlog
        _ = 16 * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
            (1 + Real.log (2 * (D : ℝ)))) := by ring

/-- Complete reduction of the previously external congruence-window assertion
to the local residue-root divisor bound. -/
theorem shiftedSquareCongruenceWindowAverageAssertion_of_rootDivisorBound
    (hroot : ShiftedSquareResidueRootDivisorBound) :
    ShiftedSquareCongruenceWindowAverageAssertion := by
  refine ⟨16, by norm_num, ?_⟩
  intro a D N ha ha0 hD _hN
  exact shiftedSquareCongruencePairs_cast_le_of_rootDivisorBound
    hroot a D N ha ha0 hD

/-- Unconditional proof of the shifted-square congruence-window average.
The constructed absolute constant is `16`. -/
theorem shiftedSquareCongruenceWindowAverageAssertion_proved :
    ShiftedSquareCongruenceWindowAverageAssertion :=
  shiftedSquareCongruenceWindowAverageAssertion_of_rootDivisorBound
    shiftedSquareResidueRootDivisorBound_proved

end

end PellPaper
