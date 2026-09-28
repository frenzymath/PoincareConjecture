import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapTipFans







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))



abbrev incidentSide (e : T.decomposition.EdgeIndex) (side : Bool) :
    T.decomposition.IncidentEdgeIndex :=
  ⟨(if side then T.decomposition.regionLeft e else T.decomposition.regionRight e, e),
    by cases side <;> simp⟩



theorem first_cap_tip_contribution (g : RiemannianMetric 2 S)
    (e : T.decomposition.EdgeIndex) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g ((T.caps (T.decomposition.edgeEndpoint e false)).coordinates (j, k))
        (T.refinement.mesh (.inl (T.decomposition.edgeEndpoint e false, (j, k))))
        (T.decomposition.edgeFromEndpoint e false (T.cut e false))) +
      (∑ side : Bool,
        ∑ p : Fin (T.bands (T.incidentSide e side)
          (T.graphs (T.incidentSide e side)).firstPiece).faces.interface.count × Bool,
        meshVertexAngleContribution g
          ((T.bands (T.incidentSide e side)
            (T.graphs (T.incidentSide e side)).firstPiece).faces.faceCoordinates p)
          (T.refinement.mesh (.inr (.inl
            ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).firstPiece⟩, p⟩)))
          (T.decomposition.edgeFromEndpoint e false (T.cut e false))) = 2 * Real.pi := by
  have hcap (s : Bool × Bool) :=
    (T.refinement.subdivision (.inl (T.decomposition.edgeEndpoint e false, s))).mesh_eq_refineByLines
  have hband (side : Bool)
      (p : Fin (T.bands (T.incidentSide e side)
        (T.graphs (T.incidentSide e side)).firstPiece).faces.interface.count × Bool) :=
    (T.refinement.subdivision (.inr (.inl
      ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).firstPiece⟩, p⟩))).mesh_eq_refineByLines
  simp_rw [show ∀ s, T.refinement.mesh (.inl (T.decomposition.edgeEndpoint e false, s)) = _ from hcap,
    show ∀ side p, T.refinement.mesh (.inr (.inl
      ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).firstPiece⟩, p⟩)) = _ from hband]
  exact FiniteChartRegionDecomposition.first_cap_tip_refined_fan
    (D := T.decomposition) (P := T.patches) (region := T.region)
    (chart := fun R => (T.chart R : S)) (caps := T.caps) (e := e) (cut := T.cut)
    (fun side => T.graphs (T.incidentSide e side))
    (fun side => T.leftCap (T.incidentSide e side))
    (fun side => T.rightCap (T.incidentSide e side))
    (fun side => T.chains (T.incidentSide e side)) g
    (fun side => T.bands (T.incidentSide e side) (T.graphs (T.incidentSide e side)).firstPiece)
    T.length_le_one
    (fun s => (T.refinement.subdivision (.inl (T.decomposition.edgeEndpoint e false, s))).refinement_lines)
    (fun side p => (T.refinement.subdivision (.inr (.inl
      ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).firstPiece⟩, p⟩))).refinement_lines)



theorem last_cap_tip_contribution (g : RiemannianMetric 2 S)
    (e : T.decomposition.EdgeIndex) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g ((T.caps (T.decomposition.edgeEndpoint e true)).coordinates (j, k))
        (T.refinement.mesh (.inl (T.decomposition.edgeEndpoint e true, (j, k))))
        (T.decomposition.edgeFromEndpoint e true (T.cut e true))) +
      (∑ side : Bool,
        ∑ p : Fin (T.bands (T.incidentSide e side)
          (T.graphs (T.incidentSide e side)).lastPiece).faces.interface.count × Bool,
        meshVertexAngleContribution g
          ((T.bands (T.incidentSide e side)
            (T.graphs (T.incidentSide e side)).lastPiece).faces.faceCoordinates p)
          (T.refinement.mesh (.inr (.inl
            ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).lastPiece⟩, p⟩)))
          (T.decomposition.edgeFromEndpoint e true (T.cut e true))) = 2 * Real.pi := by
  have hcap (s : Bool × Bool) :=
    (T.refinement.subdivision (.inl (T.decomposition.edgeEndpoint e true, s))).mesh_eq_refineByLines
  have hband (side : Bool)
      (p : Fin (T.bands (T.incidentSide e side)
        (T.graphs (T.incidentSide e side)).lastPiece).faces.interface.count × Bool) :=
    (T.refinement.subdivision (.inr (.inl
      ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).lastPiece⟩, p⟩))).mesh_eq_refineByLines
  simp_rw [show ∀ s, T.refinement.mesh (.inl (T.decomposition.edgeEndpoint e true, s)) = _ from hcap,
    show ∀ side p, T.refinement.mesh (.inr (.inl
      ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).lastPiece⟩, p⟩)) = _ from hband]
  exact FiniteChartRegionDecomposition.last_cap_tip_refined_fan
    (D := T.decomposition) (P := T.patches) (region := T.region)
    (chart := fun R => (T.chart R : S)) (caps := T.caps) (e := e) (cut := T.cut)
    (fun side => T.graphs (T.incidentSide e side))
    (fun side => T.leftCap (T.incidentSide e side))
    (fun side => T.rightCap (T.incidentSide e side))
    (fun side => T.chains (T.incidentSide e side)) g
    (fun side => T.bands (T.incidentSide e side) (T.graphs (T.incidentSide e side)).lastPiece)
    T.length_le_one
    (fun s => (T.refinement.subdivision (.inl (T.decomposition.edgeEndpoint e true, s))).refinement_lines)
    (fun side p => (T.refinement.subdivision (.inr (.inl
      ⟨⟨T.incidentSide e side, (T.graphs (T.incidentSide e side)).lastPiece⟩, p⟩))).refinement_lines)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
