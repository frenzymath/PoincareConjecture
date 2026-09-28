import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Interfaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.OuterFaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph Plane M} {lo : ℝ → ℝ}
  {a b ua wa ub wb ra rb : ℝ} (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

omit [T2Space M] in
theorem upper_segment_subset_source (i : Fin B.interface.count) :
    collarParameterEquiv.symm '' segment ℝ
      (B.interface.cut i.castSucc, lo (B.interface.cut i.castSucc) + B.interface.height i.castSucc)
      (B.interface.cut i.succ, lo (B.interface.cut i.succ) + B.interface.height i.succ) ⊆ F.source := by
  rintro z ⟨q, hq, rfl⟩
  let G := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  rw [← G.coordinates_image_upperGraph_eq_segment B.open_domain B.smooth_lower] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  have hband : collarParameterEquiv.symm (t, G.upperGraph t) ∈ B.band := by
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change (collarParameterEquiv (collarParameterEquiv.symm (t, G.upperGraph t))).1 ∈ _ ∧ _
    rw [collarParameterEquiv.apply_symm_apply]
    exact ⟨ht, (G.upperGraph_bounds ht).1.le, le_rfl⟩
  have hs := (B.band_subset_source hband).2
  change collarParameterEquiv.symm (B.cuts.coordinates B.open_domain B.smooth_lower
    (collarParameterEquiv (collarParameterEquiv.symm (t, G.upperGraph t)))) ∈ F.source at hs
  simpa only [collarParameterEquiv.apply_symm_apply] using hs

include B in
omit [T2Space M] in
theorem left_segment_subset_source :
    collarParameterEquiv.symm '' segment ℝ (a, lo a) (a + ra * ua, lo a + ra * wa) ⊆ F.source := by
  rintro z ⟨q, hq, rfl⟩
  have he : (a + ra * ua, lo a + ra * wa) = (a, lo a) + ra • (ua, wa) := by
    ext <;> simp [smul_eq_mul]
  rw [he, ← B.cuts.left.inverse_ray_image_Icc (a, lo a) (ua, wa)
    B.left_length_pos.le B.interface.left_parameter_mem] at hq
  obtain ⟨h, hh, rfl⟩ := hq
  have htarget : h ∈ B.cuts.left.parameter.target := by
    rw [← B.cuts.left.parameter_image_Icc B.left_length_pos.le B.interface.left_parameter_mem] at hh
    obtain ⟨v, hv, rfl⟩ := hh
    exact B.cuts.left.parameter.map_source
      (B.cuts.left.parameter_Icc_subset_source B.interface.left_parameter_mem hv)
  have hband : collarParameterEquiv.symm (0, h) ∈ B.band := by
    rw [B.band_eq_subgraph]
    simp only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply]
    exact ⟨by simp, hh.1, B.height_zero.symm ▸ hh.2⟩
  have hs := (B.band_subset_source hband).2
  change collarParameterEquiv.symm
    (B.cuts.coordinates B.open_domain B.smooth_lower
      (collarParameterEquiv (collarParameterEquiv.symm (0, h)))) ∈ F.source at hs
  rw [collarParameterEquiv.apply_symm_apply, B.cuts.coordinates_apply, obliqueStripMap_left,
    B.cuts.left.line_identity htarget] at hs
  exact hs

omit [T2Space M] in
theorem corner_sides_subset_source :
    segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 1) ∪
      segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 2) ⊆ F.source := by
  have himage (p q : ℝ × ℝ) :
      collarParameterEquiv.symm '' segment ℝ p q =
        segment ℝ (collarParameterEquiv.symm p) (collarParameterEquiv.symm q) :=
    image_segment ℝ collarParameterEquiv.symm.toLinearMap.toAffineMap p q
  apply union_subset
  · rw [B.firstUpperCornerBasis_zero, B.firstUpperCornerBasis_one, ← himage]
    exact B.upper_segment_subset_source B.firstCell
  · rw [B.firstUpperCornerBasis_zero, B.firstUpperCornerBasis_two,
      B.interface.first_vertex, segment_symm, ← himage]
    exact B.left_segment_subset_source

end ObliqueBandFaces

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

noncomputable def firstUpperChartBasis : AffineBasis (Fin 3) ℝ Plane :=
  affineBasisOfTriangle
    (fun j => (collarParameterEquiv.trans G.frame.symm) (B.faces.firstUpperCornerBasis j))
    (B.faces.firstUpperCornerBasis.ind.map'
      (collarParameterEquiv.trans G.frame.symm).toLinearMap.toAffineMap
      (collarParameterEquiv.trans G.frame.symm).injective)

omit [T2Space M] in
private theorem firstUpperChartSides_eq_image :
    segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1) ∪
      segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2) =
    (collarParameterEquiv.trans G.frame.symm) ''
      (segment ℝ (B.faces.firstUpperCornerBasis 0) (B.faces.firstUpperCornerBasis 1) ∪
        segment ℝ (B.faces.firstUpperCornerBasis 0) (B.faces.firstUpperCornerBasis 2)) := by
  rw [image_union]
  have himage (p q : Plane) :
      (collarParameterEquiv.trans G.frame.symm) '' segment ℝ p q =
        segment ℝ ((collarParameterEquiv.trans G.frame.symm) p)
          ((collarParameterEquiv.trans G.frame.symm) q) :=
    image_segment ℝ (collarParameterEquiv.trans G.frame.symm).toLinearMap.toAffineMap p q
  rw [himage, himage]
  rfl

omit [T2Space M] in
theorem firstUpperChartSides_subset_source :
    segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1) ∪
      segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2) ⊆ C.source := by
  rw [B.firstUpperChartSides_eq_image]
  rintro z ⟨q, hq, rfl⟩
  exact (B.faces.corner_sides_subset_source hq).2

omit [T2Space M] in
theorem carrier_subset_parent_target : B.faces.carrier ⊆ C.target := by
  intro y hy
  exact (B.faces.carrier_subset_target hy).1.1

theorem firstUpperChartSides_subset_parent :
    segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1) ∪
      segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2) ⊆
        C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier := by
  intro z hz
  have hsource := B.firstUpperChartSides_subset_source hz
  rw [B.firstUpperChartSides_eq_image] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  refine ⟨C ((collarParameterEquiv.trans G.frame.symm) q), ?_, C.left_inv hsource⟩
  exact B.faces.corner_sides_image_subset_first_upper_carrier ⟨q, hq, rfl⟩

omit [T2Space M] in

theorem core_first_upper_contact_subset_corner_sides (T : TriangleMesh)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc) :
    T.toPlaneComplex.support ∩ C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier ⊆
      segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1) ∪
        segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2) := by
  rintro z ⟨hz, y, hy, rfl⟩
  have htarget : y ∈ C.target := B.carrier_subset_parent_target
    (mem_iUnion.mpr ⟨(B.faces.firstCell, true), hy⟩)
  have hcore : y ∈ C '' T.toPlaneComplex.support :=
    ⟨C.symm y, hz, C.right_inv htarget⟩
  obtain ⟨q, hq, hqy⟩ := B.faces.first_upper_carrier_inter_subset_corner_sides
    hinterior hlower ⟨hcore, hy⟩
  rw [B.firstUpperChartSides_eq_image]
  refine ⟨q, hq, ?_⟩
  rw [← hqy]
  exact (C.left_inv (B.faces.corner_sides_subset_source hq).2).symm

theorem exists_core_refinement_first_upper_contacts (T : TriangleMesh)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc) :
    ∃ T' : TriangleMesh, T'.toPlaneComplex.support = T.toPlaneComplex.support ∧
      T'.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      ∀ t : T'.Triangle,
        (T'.triangleCarrier t.1 ∩ C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier ⊆
          frontier (T'.triangleCarrier t.1)) ∧
        (T'.triangleCarrier t.1 ∩ C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier = ∅ ∨
          ∃ (j : Fin 3) (s u : ℝ), (j = 1 ∨ j = 2) ∧
            s ∈ Icc (0 : ℝ) 1 ∧ u ∈ Icc (0 : ℝ) 1 ∧ s ≤ u ∧
            T'.triangleCarrier t.1 ∩ C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier =
              AffineMap.lineMap (B.firstUpperChartBasis 0) (B.firstUpperChartBasis j) '' Icc s u) := by
  obtain ⟨T', hs, hsub, hcontact⟩ := T.exists_refinement_with_corner_contact_subsegments
    (fun _ : Unit => B.firstUpperChartBasis)
    (fun _ : Unit => C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier)
    (fun _ => B.firstUpperChartSides_subset_parent)
    (fun _ => B.core_first_upper_contact_subset_corner_sides T hinterior hlower)
  exact ⟨T', hs, hsub, fun t => hcontact t ()⟩

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces
end PoincareConjecture.Topology.Surface
