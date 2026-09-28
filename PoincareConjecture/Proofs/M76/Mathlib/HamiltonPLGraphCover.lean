import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLGraphBlock
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonFiniteAtlas
import Mathlib.Topology.ShrinkingLemma

set_option autoImplicit false

open Set Geometry

namespace ChartedSpace

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]

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
