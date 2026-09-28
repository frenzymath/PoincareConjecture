import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Decomposition

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))

theorem region_frontier_subset_arrangement (R : D.regions) :
    frontier (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ⊆
      chartDiskBoundaryUnion D.centers D.radius := by
  rw [D.region_frontier, ← D.boundary_cover]
  rintro p hp
  obtain ⟨e, he⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨e.1, he⟩

theorem region_closure_diff_arrangement_subset (R : D.regions) :
    closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) \
      chartDiskBoundaryUnion D.centers D.radius ⊆
        connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
  rintro p ⟨hp, hK⟩
  by_contra hn
  exact hK (D.region_frontier_subset_arrangement R ⟨hp, fun hi => hn (interior_subset hi)⟩)

theorem region_closure_diff_arrangement_subset_interior (R : D.regions) :
    closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) \
      chartDiskBoundaryUnion D.centers D.radius ⊆
        interior (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
  rintro p ⟨hp, hK⟩
  by_contra hn
  exact hK (D.region_frontier_subset_arrangement R ⟨hp, hn⟩)

theorem regions_disjoint {R S : D.regions} (hne : R ≠ S) :
    Disjoint (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
      (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ S) := by
  apply disjoint_left.mpr
  intro p hp hp'
  exact hne (Subtype.ext (D.regions_distinct R R.property S S.property
    ((connectedComponentIn_eq hp).trans (connectedComponentIn_eq hp').symm)))

theorem inter_eq_arrangement_traces {R S : D.regions} (hne : R ≠ S)
    {A B : Set M}
    (hA : A \ chartDiskBoundaryUnion D.centers D.radius ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hB : B \ chartDiskBoundaryUnion D.centers D.radius ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ S) :
    A ∩ B = (A ∩ chartDiskBoundaryUnion D.centers D.radius) ∩
      (B ∩ chartDiskBoundaryUnion D.centers D.radius) := by
  ext p
  constructor
  · rintro ⟨hpA, hpB⟩
    have hpK : p ∈ chartDiskBoundaryUnion D.centers D.radius := by
      by_contra hpK
      exact disjoint_left.mp (D.regions_disjoint hne) (hA ⟨hpA, hpK⟩) (hB ⟨hpB, hpK⟩)
    exact ⟨⟨hpA, hpK⟩, hpB, hpK⟩
  · exact fun hp => ⟨hp.1.1, hp.2.1⟩

theorem region_closure_subset_assigned_pieces
    {ι : Type*} [Finite ι] (region : ι → D.regions) (piece : ι → Set M)
    (hclosed : ∀ i, IsClosed (piece i))
    (hregion : ∀ i, piece i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i)))
    {N : Set M} (hN : IsOpen N) (hcover : N ⊆ ⋃ i, piece i) (R : D.regions) :
    N ∩ closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ⊆
      ⋃ i : {i : ι // region i = R}, piece i.1 := by
  have hsub : N ∩ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ⊆
      ⋃ i : {i : ι // region i = R}, piece i.1 := by
    rintro p ⟨hpN, hpR⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hpN)
    have hpK : p ∉ chartDiskBoundaryUnion D.centers D.radius :=
      connectedComponentIn_subset _ _ hpR
    have hpi := D.region_closure_diff_arrangement_subset (region i) ⟨hregion i hi, hpK⟩
    have hiR : region i = R := by
      by_contra hne
      exact disjoint_left.mp (D.regions_disjoint hne) hpi hpR
    exact mem_iUnion.mpr ⟨⟨i, hiR⟩, hi⟩
  exact hN.inter_closure.trans
    (closure_minimal hsub (isClosed_iUnion_of_finite (fun i => hclosed i.1)))

theorem frontier_assigned_pieces_subset
    {ι : Type*} [Finite ι] (region : ι → D.regions) (piece : ι → Set M)
    (hclosed : ∀ i, IsClosed (piece i))
    (hregion : ∀ i, piece i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i))) (R : D.regions) :
    frontier (⋃ i : {i : ι // region i = R}, piece i.1) ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪ frontier (⋃ i, piece i) := by
  intro p hp
  by_cases hpK : p ∈ chartDiskBoundaryUnion D.centers D.radius
  · exact Or.inl hpK
  apply Or.inr
  have hpPiece := (isClosed_iUnion_of_finite (fun i : {i : ι // region i = R} =>
    hclosed i.1)).frontier_subset hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hpPiece
  have hpAll : p ∈ ⋃ j, piece j := mem_iUnion.mpr ⟨i.1, hi⟩
  have hpR : p ∈ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
    simpa only [i.2] using hregion i.1 hi
  have hpInt := D.region_closure_diff_arrangement_subset_interior R ⟨hpR, hpK⟩
  refine ⟨subset_closure hpAll, ?_⟩
  intro hpInterior
  apply hp.2
  have hcover := D.region_closure_subset_assigned_pieces region piece hclosed hregion
    isOpen_interior interior_subset R
  apply ((isOpen_interior.inter isOpen_interior).subset_interior_iff.mpr
    (show interior (⋃ j, piece j) ∩ interior (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ⊆
        ⋃ j : {j : ι // region j = R}, piece j.1 from
      fun _ h => hcover ⟨h.1, subset_closure (interior_subset h.2)⟩))
  exact ⟨hpInterior, hpInt⟩

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
