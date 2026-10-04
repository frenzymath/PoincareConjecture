import PoincareLib.Topology.Manifold.Smoothing.Dehn.Circles.Tubes.LocalVertexSectors
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surgery.Tubes.Branches.TargetComplex

/-! # Actual coordinate sectors at axis vertices -/

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareMT.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_raw_vertex_sectors
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : E) (C : RawSourceCrossing e f S R x y),
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

end PoincareMT.M76.Dehn.Annuli
