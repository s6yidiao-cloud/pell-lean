import Mathlib.Topology.Instances.Matrix

/-!
# Persistence of a nonzero finite determinant under matrix convergence

The finite-truncation step in `L:quantitative-two-layer-determinant` of
`main.tex` needs a topological handoff: once finite Taylor evaluation
matrices converge entrywise to an exponential evaluation matrix with nonzero
determinant, all sufficiently late truncations have nonzero determinant.

This module proves that finite-dimensional handoff for an arbitrary
topological commutative ring.  It does not prove convergence of any Taylor
series or nonvanishing of the limiting exponential determinant.
-/

namespace PellPaper

/-- Entrywise convergence of square matrices is convergence in the matrix
product topology. -/
theorem tendsto_matrix_of_tendsto_entries
    {X n R : Type*} [TopologicalSpace X] [TopologicalSpace R]
    {l : Filter X} {A : X → Matrix n n R} {M : Matrix n n R}
    (hentry : ∀ i j, Filter.Tendsto (fun x => A x i j) l (nhds (M i j))) :
    Filter.Tendsto A l (nhds M) := by
  change Filter.Tendsto (fun x i j => A x i j) l (nhds (fun i j => M i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact hentry i j

/-- Matrix convergence transports through the determinant. -/
theorem tendsto_det_of_tendsto_matrix
    {X n R : Type*} [TopologicalSpace X] [TopologicalSpace R]
    [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {l : Filter X} {A : X → Matrix n n R} {M : Matrix n n R}
    (hA : Filter.Tendsto A l (nhds M)) :
    Filter.Tendsto (fun x => (A x).det) l (nhds M.det) := by
  simpa [Function.comp_def] using
    (continuous_id.matrix_det.continuousAt.tendsto.comp hA)

/-- A nonzero limiting determinant persists eventually along every convergent
matrix family. -/
theorem eventually_det_ne_zero_of_tendsto_matrix
    {X n R : Type*} [TopologicalSpace X] [TopologicalSpace R] [T1Space R]
    [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {l : Filter X} {A : X → Matrix n n R} {M : Matrix n n R}
    (hA : Filter.Tendsto A l (nhds M)) (hdet : M.det ≠ 0) :
    ∀ᶠ x in l, (A x).det ≠ 0 := by
  exact (tendsto_det_of_tendsto_matrix hA).eventually_ne hdet

/-- The same eventual nonvanishing conclusion from entrywise convergence,
which is the form directly supplied by finite Taylor truncations. -/
theorem eventually_det_ne_zero_of_tendsto_entries
    {X n R : Type*} [TopologicalSpace X] [TopologicalSpace R] [T1Space R]
    [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {l : Filter X} {A : X → Matrix n n R} {M : Matrix n n R}
    (hentry : ∀ i j, Filter.Tendsto (fun x => A x i j) l (nhds (M i j)))
    (hdet : M.det ≠ 0) :
    ∀ᶠ x in l, (A x).det ≠ 0 := by
  exact eventually_det_ne_zero_of_tendsto_matrix
    (tendsto_matrix_of_tendsto_entries hentry) hdet

/-- For a sequence of finite truncations, entrywise convergence to a
nonsingular limit gives a concrete tail on which every determinant is
nonzero. -/
theorem exists_tail_det_ne_zero_of_tendsto_entries_atTop
    {n R : Type*} [TopologicalSpace R] [T1Space R]
    [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    (A : ℕ → Matrix n n R) (M : Matrix n n R)
    (hentry : ∀ i j, Filter.Tendsto (fun k => A k i j) Filter.atTop
      (nhds (M i j)))
    (hdet : M.det ≠ 0) :
    ∃ N : ℕ, ∀ k ≥ N, (A k).det ≠ 0 := by
  exact Filter.eventually_atTop.mp
    (eventually_det_ne_zero_of_tendsto_entries hentry hdet)

end PellPaper
