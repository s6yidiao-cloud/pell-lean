import Pell.QuadraticAlgebraFieldDiscriminantEquality
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# The unramified prime-ideal dichotomy in a concrete quadratic field

For a positive fundamental discriminant `D` and any rational prime `p` not
dividing `D`, including `p = 2`, the actual ring of integers has either one
prime over `(p)` of norm `p²`, or two distinct primes over `(p)`, both of norm
`p`.  The selected ideals are maximal, have exactly the displayed contraction,
and exhaust all maximal ideals over `(p)`.

The proof uses the exact field discriminant, the discriminant/unramified
criterion, and the degree-two ramification/inertia sum.  This proves no
identification with a quadratic character or congruence condition.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_unramifiedDichotomy_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

private theorem positive_sum_eq_two_dichotomy {α : Type*} [Fintype α]
    (f : α → ℕ) (hpos : ∀ a, 0 < f a) (hsum : ∑ a, f a = 2) :
    (∃ a, f a = 2 ∧ ∀ b, b = a) ∨
      ∃ a b, a ≠ b ∧ f a = 1 ∧ f b = 1 ∧ ∀ c, c = a ∨ c = b := by
  classical
  by_cases htwo : ∃ a, f a = 2
  · obtain ⟨a, ha⟩ := htwo
    left
    refine ⟨a, ha, ?_⟩
    intro b
    by_contra hba
    have hbmem : b ∈ Finset.univ.erase a :=
      Finset.mem_erase.mpr ⟨hba, Finset.mem_univ _⟩
    have hble : f b ≤ ∑ c ∈ Finset.univ.erase a, f c :=
      Finset.single_le_sum (fun c _ => Nat.zero_le (f c)) hbmem
    have hbpos := hpos b
    have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
    omega
  · have hone : ∀ a, f a = 1 := by
      intro a
      have hale : f a ≤ ∑ b, f b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (f b)) (Finset.mem_univ a)
      have hapos := hpos a
      have hane : f a ≠ 2 := fun ha => htwo ⟨a, ha⟩
      omega
    have hcard : (Finset.univ : Finset α).card = 2 := by
      simpa [hone] using hsum
    obtain ⟨a, b, hab, habuniv⟩ := Finset.card_eq_two.mp hcard
    right
    refine ⟨a, b, hab, hone a, hone b, ?_⟩
    intro c
    have hc : c ∈ ({a, b} : Finset α) := by rw [← habuniv]; exact Finset.mem_univ _
    simpa using hc

private theorem unramified_inertia_sum_eq_two
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : ¬ p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : Fact (Nat.Prime p) := ⟨hp⟩
    ∑ Q : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      Q.1.inertiaDeg ℤ = 2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  dsimp only
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp
  have hdisc : NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) = (D : ℤ) := by
    change rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant D hD =
      (D : ℤ)
    exact rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD
  have hnotdvd : ¬ (p : ℤ) ∣ NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) := by
    rw [hdisc]
    exact_mod_cast hpD
  have hunram := (NumberField.not_dvd_discr_iff_forall_liesOver
    (rationalQuadraticAlgebra (D : ℤ))
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) hpz).mp hnotdvd
  have heq : ∀ Q : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      Q.1.ramificationIdx ℤ = 1 := by
    intro Q
    exact Ideal.ramificationIdx_eq_one_iff.mpr
      (hunram Q.1 (inferInstance : Q.1.IsMaximal) (inferInstance : Q.1.LiesOver _))
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (p := Ideal.span ({(p : ℤ)} : Set ℤ))
    (S := NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
  simp only [heq, one_mul] at hsum
  rw [NumberField.RingOfIntegers.rank, rationalQuadraticAlgebra_finrank_eq_two] at hsum
  exact hsum

/-- At every rational prime not dividing a positive fundamental discriminant,
the concrete quadratic ring of integers has exactly one prime of norm `p²`
or exactly two distinct primes of norm `p` over `(p)`.  This includes `p = 2`.
The theorem does not decide the alternative using a character or congruence. -/
theorem rationalQuadraticAlgebra_unramified_primeIdeal_norm_dichotomy
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : ¬ p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : Fact (Nat.Prime p) := ⟨hp⟩
    (∃ P : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      P.IsMaximal ∧ P.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) ∧
      Ideal.absNorm P = p ^ 2 ∧
      ∀ Q : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Q.IsMaximal → Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P) ∨
    (∃ P Q : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      P ≠ Q ∧ P.IsMaximal ∧ Q.IsMaximal ∧
      P.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) ∧
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) ∧
      Ideal.absNorm P = p ∧ Ideal.absNorm Q = p ∧
      ∀ R : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        R.IsMaximal → R.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → R = P ∨ R = Q) := by
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  dsimp only
  let A := (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
  have hpos : ∀ Q : A, 0 < Q.1.inertiaDeg ℤ := fun Q => Ideal.inertiaDeg_pos Q.1 ℤ
  have hsum : ∑ Q : A, Q.1.inertiaDeg ℤ = 2 :=
    unramified_inertia_sum_eq_two D p hD hp hpD
  have hcases := positive_sum_eq_two_dichotomy (fun Q : A => Q.1.inertiaDeg ℤ) hpos hsum
  rcases hcases with ⟨P, hPdeg, huniq⟩ | ⟨P, Q, hPQ, hPdeg, hQdeg, hexhaust⟩
  · left
    refine ⟨P.1, inferInstance, (Ideal.over_def P.1 _).symm, ?_, ?_⟩
    · rw [← Ideal.pow_inertiaDeg p P.1, hPdeg]
    · intro Q hQmax hQunder
      let _ : Q.IsPrime := hQmax.isPrime
      let _ : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := ⟨hQunder.symm⟩
      exact congrArg Subtype.val
        (huniq (Ideal.primesOver.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) Q))
  · right
    refine ⟨P.1, Q.1, ?_, inferInstance, inferInstance,
      (Ideal.over_def P.1 _).symm, (Ideal.over_def Q.1 _).symm, ?_, ?_, ?_⟩
    · exact fun h => hPQ (Subtype.ext h)
    · rw [← Ideal.pow_inertiaDeg p P.1, hPdeg, pow_one]
    · rw [← Ideal.pow_inertiaDeg p Q.1, hQdeg, pow_one]
    · intro R hRmax hRunder
      let _ : R.IsPrime := hRmax.isPrime
      let _ : R.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := ⟨hRunder.symm⟩
      rcases hexhaust (Ideal.primesOver.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) R) with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)

end

end PellPaper
