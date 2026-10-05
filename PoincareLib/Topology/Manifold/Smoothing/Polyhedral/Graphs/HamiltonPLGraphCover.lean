import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.HamiltonPLGraphBlock
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonFiniteAtlas
import Mathlib.Topology.ShrinkingLemma

/-!
# Compact cores of a finite PL atlas

Shrink a finite compatible PL chart cover to compact cores.
These are the domains for the supported graph blocks and the
compact topological input for the finite PL embedding. See
Hamilton 1976, p. 69 and M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry

namespace ChartedSpace

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- The actual finite PL chart cover has compact cores whose
interiors cover the whole manifold. Each core remains inside
its original chart. See Hamilton p. 69 and derivation 258. -/
theorem exists_finite_compact_PL_chart_cover_with_interiors
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := E)) :
    ∃ (s : Finset (OpenPartialHomeomorph M E))
      (Q : s → Set M),
      (∀ i j : s, (i : OpenPartialHomeomorph M E).symm.trans
        (j : OpenPartialHomeomorph M E) ∈ piecewiseAffineGroupoid E) ∧
      (∀ i, IsCompact (Q i)) ∧ (∀ i, Q i ⊆ (i : OpenPartialHomeomorph M E).source) ∧
      (∀ x : M, ∃ i, x ∈ interior (Q i)) := by
  classical
  obtain ⟨s, hcompat, hcover⟩ :=
    exists_finite_piecewiseAffine_chart_cover (E := E) hlocal
  let u : s → Set M := fun i => (i : OpenPartialHomeomorph M E).source
  have hu : ∀ i, IsOpen (u i) := fun i => (i : OpenPartialHomeomorph M E).open_source
  have huf (x : M) (_ : x ∈ (univ : Set M)) : {i : s | x ∈ u i}.Finite :=
    Set.toFinite _
  have huU : (univ : Set M) ⊆ ⋃ i : s, u i := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨v, hvU, hv, hvcl⟩ :=
    exists_subset_iUnion_closure_subset (s := (univ : Set M)) isClosed_univ hu huf huU
  let Q : ∀ i : s, Set M := fun i => closure (v i)
  have hQ (i : s) : IsCompact (Q i) := isClosed_closure.isCompact
  have hQs (i : s) : Q i ⊆ u i := hvcl i
  refine ⟨s, Q, hcompat, hQ, hQs, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hvU (mem_univ x))
  exact ⟨i, (hv i).subset_interior_iff.mpr subset_closure hi⟩

/-- The actual finite PL chart cover has compact cores inside
the same charts and covering the whole manifold. The topology
remains the given one. See Hamilton p. 69 and M76 derivation 258. -/
theorem exists_finite_compact_PL_chart_cover
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := E)) :
    ∃ (s : Finset (OpenPartialHomeomorph M E))
      (Q : s → Set M),
      (∀ i j : s, (i : OpenPartialHomeomorph M E).symm.trans
        (j : OpenPartialHomeomorph M E) ∈ piecewiseAffineGroupoid E) ∧
      (∀ i, IsCompact (Q i)) ∧ (∀ i, Q i ⊆ (i : OpenPartialHomeomorph M E).source) ∧
      (∀ x : M, ∃ i, x ∈ Q i) := by
  obtain ⟨s, Q, hcompat, hQ, hQs, hcover⟩ :=
    exists_finite_compact_PL_chart_cover_with_interiors hlocal
  refine ⟨s, Q, hcompat, hQ, hQs, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := hcover x
  exact ⟨i, interior_subset hxi⟩

end ChartedSpace
