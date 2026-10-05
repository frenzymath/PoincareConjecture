import PoincareLib.Topology.Manifold.Smoothing.Dehn.Circles.Tubes.LocalBranchTargetComplex
import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleArc.OriginalVertexCoordinateSectors

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in
set_option maxHeartbeats 800000 in
/-- Every actual selected vertex has four finite PL sector balls in a
constructed raw chart, with the complete local sheet marks retained.
The local labels are permitted to exchange at the next vertex. -/
theorem ComponentBranchModel.exists_raw_vertex_sectors
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : V2) (C : RawCrossingChart e f R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      (∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) ∧
      (∀ j : Fin 2,
        ((D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
        (D.complex.closedStar p).space ∩
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}) ∧
      ∀ signs : Fin 2 → Bool,
        let V := D.complex.barycentricDualBlock {p}
        let cuts := {z | ∀ j : Fin 2,
          if signs j then 0 ≤ C.chart (D.inverse z) j.castSucc
          else C.chart (D.inverse z) j.castSucc ≤ 0}
        IsFinitePLBallPair V3 (V.space ∩ cuts)
          {z | z ∈ V.space ∧ z ∈ cuts ∧
            (z ∈ (V.link p).space ∨ ∃ j : Fin 2, C.chart (D.inverse z) j.castSucc = 0)} := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨x, y, C, hC, hface, haxis, hsheet⟩ := D.exists_marked_raw_star p hp
  have hpK : p ∈ D.complex.vertices := D.axis_le hp
  have hpstar : p ∈ (D.complex.closedStar p).space := by
    apply (D.complex.closedStar p).vertices_subset_space
    exact ⟨hpK, by simpa using (show {p} ∈ D.complex.faces from hpK)⟩
  have hpaxis := D.axis.vertices_subset_space hp
  have hpzero := (haxis p hpstar).mp hpaxis
  have hpcore : (D.inverse p : X) ∈ interior D.core := by
    apply D.core_neighborhood
    obtain ⟨a, ha, hap⟩ := D.axis_space.subset hpaxis
    refine ⟨a, ha, ?_⟩
    exact (D.graph_separates _ (D.inverse p).property _
      ((D.graph_inverse p (D.complex.vertices_subset_space hpK)).trans hap.symm)).symm
  refine ⟨x, y, C, hC, hface, haxis, hsheet, fun signs => ?_⟩
  have hball := isFinitePLBallPair_original_vertex_coordinate_sector D.complex D.homeomorph
    D.inverse D.inverse_value p hpK hpcore C.chart
    (by convert hC using 1; congr 3; exact Subsingleton.elim _ _)
    (by convert hface using 1; congr 2; exact Subsingleton.elim _ _)
    (by intro j; fin_cases j; exact hpzero.2.1; exact hpzero.2.2) signs
  dsimp only at hball ⊢
  convert hball using 1
  congr 8
  funext z
  congr 6
  exact Subsingleton.elim _ _

end PoincareMT.M76.Dehn
