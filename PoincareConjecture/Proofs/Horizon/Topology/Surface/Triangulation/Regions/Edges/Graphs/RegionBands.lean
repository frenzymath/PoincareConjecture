import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Interfaces

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedGraphPiece

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b}
  {ua wa ub wb δ ra rb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  (B : G.FixedStripBandFaces P δ ra rb)

omit [T2Space M]

theorem FixedStripBandFaces.baseArc_subset_carrier (hab : a < b) :
    (D.edge e.1 e.2).map '' Icc a b ⊆ B.faces.carrier := by
  rw [← G.strip_axis_image P hab, B.carrier_eq_fixed_strip]
  rintro p ⟨t, ht, rfl⟩
  exact ⟨(t, 0), ⟨ht, le_rfl, (B.height_bounds ht).1.le⟩, rfl⟩

theorem FixedStripBandFaces.carrier_subset_region_closure
    (hregion : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
      G.strip P (t, z) ∈ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)) :
    B.faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
  rw [B.carrier_eq_fixed_strip]
  rintro p ⟨⟨t, z⟩, ⟨ht, hz, hzh⟩, rfl⟩
  exact hregion t ht z hz (hzh.trans_lt (B.height_bounds ht).2)

theorem FixedStripBandFaces.carrier_inter_arrangement (hab : a < b)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
      (G.strip P (t, z) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0)) :
    B.faces.carrier ∩ chartDiskBoundaryUnion D.centers D.radius =
      (D.edge e.1 e.2).map '' Icc a b := by
  apply Subset.antisymm
  · rintro p ⟨hp, hK⟩
    rw [B.carrier_eq_fixed_strip] at hp
    obtain ⟨⟨t, z⟩, ⟨ht, hz, hzh⟩, rfl⟩ := hp
    have hz0 := (hzero t ht z hz (hzh.trans_lt (B.height_bounds ht).2)).mp hK
    subst z
    rw [← G.strip_axis_image P hab]
    exact ⟨t, ht, rfl⟩
  · intro p hp
    refine ⟨B.baseArc_subset_carrier hab hp, ?_⟩
    rw [← G.strip_axis_image P hab] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact (hzero t ht 0 le_rfl ((B.height_bounds ht).1.trans (B.height_bounds ht).2)).mpr rfl

theorem FixedStripBandFaces.carrier_diff_arrangement_subset_region
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
      (G.strip P (t, z) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0))
    (hpositive : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 < z → z < δ →
      G.strip P (t, z) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) :
    B.faces.carrier \ chartDiskBoundaryUnion D.centers D.radius ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
  rintro p ⟨hp, hK⟩
  rw [B.carrier_eq_fixed_strip] at hp
  obtain ⟨⟨t, z⟩, ⟨ht, hz, hzh⟩, rfl⟩ := hp
  have hδ := hzh.trans_lt (B.height_bounds ht).2
  have hne : z ≠ 0 := fun he => hK ((hzero t ht z hz hδ).mpr he)
  exact hpositive t ht z (lt_of_le_of_ne hz hne.symm) hδ

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedGraphPiece
