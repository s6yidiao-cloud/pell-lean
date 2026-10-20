import Pell.UniformExceptional

/-!
# Injecting regulator exceptions into the Pell exceptional set

The class-number argument associates a real quadratic field with its
fundamental discriminant.  The arithmetic assertion that a small regulator
forces a small fundamental Pell solution is deliberately an explicit
hypothesis below.  This file proves the finite combinatorial consequence:
injectivity of the discriminant map turns that assertion into a cardinality
bound by the Pell exceptional set.
-/

namespace PellPaper

open Set
open Filter

noncomputable section

/-- The indices in a finite family whose discriminant is below the natural
cutoff and whose regulator parameter is below `T`. -/
noncomputable def classRegulatorExceptionalSet {ι : Type*}
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (X : ℕ) (T : ℝ) : Finset ι :=
  by
    classical
    exact s.filter fun i ↦ D i ≤ X ∧ r i < T

/-- Membership exposes both endpoints of the finite class-side exceptional
set. -/
theorem mem_classRegulatorExceptionalSet {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {D : ι → ℕ} {r : ι → ℝ} {X : ℕ} {T : ℝ} {i : ι} :
    i ∈ classRegulatorExceptionalSet s D r X T ↔
      i ∈ s ∧ D i ≤ X ∧ r i < T := by
  classical
  simp [classRegulatorExceptionalSet]

/-- A discriminant-injective finite family of regulator exceptions injects
into the Pell exceptional set.  The hypothesis `htransfer` is precisely the
field/unit comparison required by the class-number argument; it is not
asserted or reconstructed here. -/
theorem classRegulatorExceptional_card_le_exceptionalSet
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (θ T : ℝ) (X : ℕ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ X → r i < T →
      SmallFundamentalSolution θ (D i)) :
    (classRegulatorExceptionalSet s D r X T).card ≤
      (exceptionalSet θ X).card := by
  classical
  let t := classRegulatorExceptionalSet s D r X T
  have hmaps : Set.MapsTo D (↑t : Set ι) (↑(exceptionalSet θ X) : Set ℕ) := by
    intro i hi
    have hi' : i ∈ t := hi
    obtain ⟨his, hiX, hir⟩ := mem_classRegulatorExceptionalSet.mp hi'
    have hsmall : SmallFundamentalSolution θ (D i) := htransfer i his hiX hir
    have hpos : 0 < D i := (positive_nonsquare_of_smallFundamentalSolution hsmall).1
    exact mem_exceptionalSet.mpr ⟨Nat.succ_le_iff.mpr hpos, hiX, hsmall⟩
  have hinj : Set.InjOn D (↑t : Set ι) := by
    intro i hi j hj hEq
    have hi' : i ∈ t := hi
    have hj' : j ∈ t := hj
    exact hDinj (mem_classRegulatorExceptionalSet.mp hi').1
      (mem_classRegulatorExceptionalSet.mp hj').1 hEq
  change t.card ≤ (exceptionalSet θ X).card
  exact Finset.card_le_card_of_injOn D hmaps hinj

/-- The preceding injection stated in the notation `EInt` used for the Pell
exceptional count. -/
theorem classRegulatorExceptional_card_le_EInt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (θ T : ℝ) (X : ℕ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ X → r i < T →
      SmallFundamentalSolution θ (D i)) :
    (classRegulatorExceptionalSet s D r X T).card ≤ EInt θ X := by
  simpa only [EInt] using
    classRegulatorExceptional_card_le_exceptionalSet s D r θ T X hDinj htransfer

/-- Any real pointwise bound for the Pell count at the integral cutoff transfers
to the class-side regulator exceptions.  This is useful because the uniform
Pell proposition is stated for the real-cutoff count `E`. -/
theorem classRegulatorExceptional_card_le_of_E_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (θ T : ℝ) (X : ℕ) (B : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ X → r i < T →
      SmallFundamentalSolution θ (D i))
    (hbound : E θ (X : ℝ) ≤ B) :
    ((classRegulatorExceptionalSet s D r X T).card : ℝ) ≤ B := by
  have hcard := classRegulatorExceptional_card_le_EInt s D r θ T X hDinj htransfer
  have hcard' : ((classRegulatorExceptionalSet s D r X T).card : ℝ) ≤
      (EInt θ X : ℝ) := by
    exact_mod_cast hcard
  have hEInt : (EInt θ X : ℝ) ≤ B := by
    simpa [E] using hbound
  exact hcard'.trans hEInt

/-- The preceding transfer with the pointwise conclusion supplied by the
uniform exceptional-set proposition.  A use of `UniformExceptionalEstimate`
first chooses its absolute constants and a sufficiently large `X`; at that
point its conclusion is exactly `huniform`. -/
theorem classRegulatorExceptional_card_le_uniform_pointwise
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ)
    (θ T cSave C : ℝ) (X : ℕ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ X → r i < T →
      SmallFundamentalSolution θ (D i))
    (huniform : E θ (X : ℝ) ≤
      C * (X : ℝ) ^ (1 - cSave / (uniformQ θ : ℝ) ^ 2)) :
    ((classRegulatorExceptionalSet s D r X T).card : ℝ) ≤
      C * (X : ℝ) ^ (1 - cSave / (uniformQ θ : ℝ) ^ 2) := by
  exact classRegulatorExceptional_card_le_of_E_bound s D r θ T X _ hDinj
    htransfer huniform

/-- The same injection at a real cutoff: the class-side natural cutoff is the
natural floor used in the definition of `E`. -/
theorem classRegulatorExceptional_card_le_E
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (θ T X : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ ⌊X⌋₊ → r i < T →
      SmallFundamentalSolution θ (D i)) :
    ((classRegulatorExceptionalSet s D r ⌊X⌋₊ T).card : ℝ) ≤ E θ X := by
  have hcard := classRegulatorExceptional_card_le_EInt s D r θ T ⌊X⌋₊ hDinj
    htransfer
  have hcard' : ((classRegulatorExceptionalSet s D r ⌊X⌋₊ T).card : ℝ) ≤
      (EInt θ ⌊X⌋₊ : ℝ) := by
    exact_mod_cast hcard
  simpa [E] using hcard'

/-- A uniform Pell exceptional-set estimate gives uniform cardinality bounds
for the regulator-small subfamilies.  The abstract hypothesis `htransfer` is
the sole field-to-Pell input: it says that regulator height below `θ` yields a
Pell fundamental solution below the corresponding `D^θ` threshold. -/
theorem eventually_regulatorSmall_card_le_uniform
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (cSave : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ θ i, i ∈ s → r i < θ →
      SmallFundamentalSolution θ (D i))
    (hUniform : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ, 3 ≤ θ →
        UniformAdmissible cExc θ X →
          ((classRegulatorExceptionalSet s D r ⌊X⌋₊ θ).card : ℝ) ≤
            C * X ^ (1 - cSave / (uniformQ θ : ℝ) ^ 2) := by
  obtain ⟨_, cExc, C, hcExc, hC, hbound⟩ := hUniform
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hbound] with X hX
  intro θ hθ hadmissible
  exact (classRegulatorExceptional_card_le_E s D r θ θ X hDinj
    (fun i hi _ hir ↦ htransfer θ i hi hir)).trans
      (hX θ hθ hadmissible)

/-- If the ambient finite family is already restricted by the discriminant
cutoff, only the regulator filter needs to be written. -/
theorem regulatorSmall_card_le_EInt_of_cutoff
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (θ T : ℝ) (X : ℕ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (hcutoff : ∀ i, i ∈ s → D i ≤ X)
    (htransfer : ∀ i, i ∈ s → r i < T →
      SmallFundamentalSolution θ (D i)) :
    (s.filter fun i ↦ r i < T).card ≤ EInt θ X := by
  classical
  let t := s.filter fun i ↦ r i < T
  have hmaps : Set.MapsTo D (↑t : Set ι) (↑(exceptionalSet θ X) : Set ℕ) := by
    intro i hi
    have hi' : i ∈ t := hi
    have hmem : i ∈ s.filter (fun i ↦ r i < T) := by simpa [t] using hi'
    have his : i ∈ s := (Finset.mem_filter.mp hmem).1
    have hir : r i < T := (Finset.mem_filter.mp hmem).2
    have hiX : D i ≤ X := hcutoff i his
    have hsmall : SmallFundamentalSolution θ (D i) := htransfer i his hir
    have hpos : 0 < D i := (positive_nonsquare_of_smallFundamentalSolution hsmall).1
    exact mem_exceptionalSet.mpr ⟨Nat.succ_le_iff.mpr hpos, hiX, hsmall⟩
  have hinj : Set.InjOn D (↑t : Set ι) := by
    intro i hi j hj hEq
    have hi' : i ∈ t := hi
    have hj' : j ∈ t := hj
    have himem : i ∈ s.filter (fun i ↦ r i < T) := by simpa [t] using hi'
    have hjmem : j ∈ s.filter (fun i ↦ r i < T) := by simpa [t] using hj'
    exact hDinj (Finset.mem_filter.mp himem).1
      (Finset.mem_filter.mp hjmem).1 hEq
  change t.card ≤ EInt θ X
  change t.card ≤ (exceptionalSet θ X).card
  exact Finset.card_le_card_of_injOn D hmaps hinj

end

end PellPaper
