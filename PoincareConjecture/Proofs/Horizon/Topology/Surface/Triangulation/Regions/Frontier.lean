


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions
import Mathlib.Topology.Connected.LocallyConnected









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Topology


theorem frontier_connectedComponentIn_compl_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hK : IsClosed K) (x : X) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  intro y hy
  by_contra hyK
  have hyV : y ∈ connectedComponentIn Kᶜ y := mem_connectedComponentIn hyK
  have hV : IsOpen (connectedComponentIn Kᶜ y) := hK.isOpen_compl.connectedComponentIn
  obtain ⟨z, hzV, hzU⟩ := mem_closure_iff.mp (frontier_subset_closure hy) _ hV hyV
  have heq : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y :=
    (connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzV).symm
  have hyU : y ∈ connectedComponentIn Kᶜ x := heq.symm ▸ hyV
  have hU : IsOpen (connectedComponentIn Kᶜ x) := hK.isOpen_compl.connectedComponentIn
  have hmem : y ∈ connectedComponentIn Kᶜ x ∩ frontier (connectedComponentIn Kᶜ x) :=
    ⟨hyU, hy⟩
  rw [hU.inter_frontier_eq] at hmem
  exact hmem

end Poincare.Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

omit [T2Space M] in

theorem chart_image_frontier_of_isCompact_closure (p : M) {U : Set M}
    (hcompact : IsCompact (closure U))
    (hsource : closure U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) p) '' frontier U =
      frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) p) '' U) := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
  change closure U ⊆ e.source at hsource
  have himage : e.IsImage U (e '' U) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (e.injOn (hsource (subset_closure hy)) hx hxy) ▸ hy
    · exact mem_image_of_mem e
  have hclosure : closure (e '' U) = e '' closure U :=
    (image_closure_of_isCompact hcompact (e.continuousOn.mono hsource)).symm
  have htarget : closure (e '' U) ⊆ e.target := by
    rw [hclosure]
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hsource hx)
  simpa only [inter_eq_right.mpr (frontier_subset_closure.trans hsource),
    inter_eq_right.mpr (frontier_subset_closure.trans htarget)] using himage.frontier.image_eq

omit [T2Space M] in

theorem infinite_frontier_of_precompact_chart_region (p : M) {U : Set M}
    (hopen : IsOpen U) (hne : U.Nonempty) (hcompact : IsCompact (closure U))
    (hsource : closure U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    (frontier U).Infinite := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
  have hbounded : Bornology.IsBounded (e '' U) :=
    (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isBounded.subset
      (image_mono subset_closure)
  have hi := Poincare.Topology.Plane.infinite_frontier_of_isOpen
    (e.isOpen_image_of_subset_source hopen (subset_closure.trans hsource))
    hbounded (hne.image e)
  intro hfinite
  apply hi
  rw [← chart_image_frontier_of_isCompact_closure p hcompact hsource]
  exact hfinite.image e

omit [T2Space M] in

theorem isClosed_chartDiskBoundaryUnion (s : Finset M) (r : M → ℝ) :
    IsClosed (chartDiskBoundaryUnion s r) :=
  isClosed_biUnion_finset (fun _ _ => isClosed_frontier)


theorem isCompact_chartDiskBoundaryUnion (s : Finset M) (r : M → ℝ)
    (htarget : ∀ p ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) :
    IsCompact (chartDiskBoundaryUnion s r) := by
  apply s.isCompact_biUnion
  intro p hp
  have hcompact := isCompact_chart_closedBall p (htarget p hp)
  exact hcompact.of_isClosed_subset isClosed_frontier hcompact.isClosed.frontier_subset



theorem exists_nonvertex_mem_frontier_complementary_component
    (s : Finset M) (r : M → ℝ) (hpos : ∀ p ∈ s, 0 < r p)
    (htarget : ∀ p ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    (hcover : (⋃ p ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p)) = (univ : Set M))
    (x : M) (hx : x ∉ chartDiskBoundaryUnion s r) {V : Set M} (hV : V.Finite) :
    ∃ y ∈ frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x),
      y ∈ chartDiskBoundaryUnion s r ∧ y ∉ V := by
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  obtain ⟨p, _, _, _, hc, hs⟩ :=
    exists_chart_disk_containing_complementary_component s r hpos htarget hcover x hx
  have hclosed := isClosed_chartDiskBoundaryUnion s r
  have hi := infinite_frontier_of_precompact_chart_region p
    hclosed.isOpen_compl.connectedComponentIn ⟨x, mem_connectedComponentIn hx⟩ hc hs
  have hnsub : ¬ frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ⊆ V :=
    fun h => hi (hV.subset h)
  obtain ⟨y, hy, hyV⟩ := Set.not_subset.mp hnsub
  exact ⟨y, hy, Poincare.Topology.frontier_connectedComponentIn_compl_subset hclosed x hy, hyV⟩



theorem exists_interior_edge_mem_frontier_complementary_component
    {I : Type*} [Finite I] (s : Finset M) (r : M → ℝ)
    (hpos : ∀ p ∈ s, 0 < r p)
    (htarget : ∀ p ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    (hcover : (⋃ p ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p)) = (univ : Set M))
    (edge : I → ℝ → M)
    (hboundary : (⋃ i, edge i '' Icc (0 : ℝ) 1) = chartDiskBoundaryUnion s r)
    (x : M) (hx : x ∉ chartDiskBoundaryUnion s r) :
    ∃ i t, t ∈ Ioo (0 : ℝ) 1 ∧
      edge i t ∈ frontier (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ∧
      ∀ j, edge i t ≠ edge j 0 ∧ edge i t ≠ edge j 1 := by
  let V : Set M := ⋃ i, {edge i 0, edge i 1}
  have hV : V.Finite := finite_iUnion (fun i => (finite_singleton (edge i 1)).insert _)
  obtain ⟨y, hy, hyK, hyV⟩ := exists_nonvertex_mem_frontier_complementary_component
    s r hpos htarget hcover x hx hV
  rw [← hboundary] at hyK
  obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hyK
  have hends : ∀ j, edge i t ≠ edge j 0 ∧ edge i t ≠ edge j 1 := by
    intro j
    constructor
    · intro h
      exact hyV (mem_iUnion.mpr ⟨j, Or.inl h⟩)
    · intro h
      exact hyV (mem_iUnion.mpr ⟨j, Or.inr h⟩)
  have hzero : t ≠ 0 := fun h => (hends i).1 (congrArg (edge i) h)
  have hone : t ≠ 1 := fun h => (hends i).2 (congrArg (edge i) h)
  exact ⟨i, t, ⟨lt_of_le_of_ne ht.1 hzero.symm, lt_of_le_of_ne ht.2 hone⟩, hy, hends⟩

end PoincareConjecture.Topology.Surface
