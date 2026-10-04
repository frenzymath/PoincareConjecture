import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Affine.ConvexFrontierCoordinateQuadrants
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateFourRegionIncidence

/-!
# The unchanged convex target's actual four-region diagram

Literal height/transverse coordinate predicates give the
complete disk-and-arc diagram for prescribed boundary graph
and region gluing. Both actual pole values and all full graph
contacts are retained. See Alexander 1924, pp. 6--8, Hudson
1969, pp. 15--19 and M76 derivation 286s.
-/

set_option autoImplicit false

open Set Geometry CoordinateFourRegions

namespace Geometry.SimplicialComplex

/-- The actual convex target supplies the full prescribed-map
gluing diagram with fixed literal coordinate labels. Each
region's graph contact is its entire two-arc rim, distinct
arcs meet exactly at the original two poles, and the regions
cover the entire frontier. See Alexander pp. 6--8 and
M76 derivation 286s. -/
theorem coordinate_frontier_marked_diagram
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hKC : K.space = C) (hzero : (0 : (ℝ × ℝ) × ℝ) ∈ interior C)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (haC : ((0, a), 0) ∈ frontier C) (hbC : ((0, b), 0) ∈ frontier C) :
    (∀ i, IsFinitePLBallPair ℝ (arc (frontier C) i)
      {((0, a), 0), ((0, b), 0)}) ∧
    Pairwise (fun i j => arc (frontier C) i ∩ arc (frontier C) j =
      {((0, a), 0), ((0, b), 0)}) ∧
    (∀ i, IsFinitePLBallPair (ℝ × ℝ) (region (frontier C) i)
      (arc (frontier C) (false, i.2) ∪ arc (frontier C) (true, i.1))) ∧
    (∀ i, region (frontier C) i ∩ graph (frontier C) =
      arc (frontier C) (false, i.2) ∪ arc (frontier C) (true, i.1)) ∧
    Pairwise (fun i j => region (frontier C) i ∩ region (frontier C) j ⊆
      arc (frontier C) (false, i.2) ∪ arc (frontier C) (true, i.1)) ∧
    (⋃ i, region (frontier C) i) = frontier C ∧
    (⋃ i, arc (frontier C) i) = graph (frontier C) := by
  obtain ⟨hArcH, hArcT, hRegion⟩ :=
    K.isFinitePLBallPair_coordinate_frontier_quadrants hK hC hcv hKC hzero ha hb haC hbC
  have haxis := hcv.frontier_inter_coordinate_planes_eq_poles hzero ha hb haC hbC
  refine ⟨?_, ?_, ?_, region_inter_graph _, region_contacts _, iUnion_region _, iUnion_arc _⟩
  · rintro ⟨i, j⟩
    cases i
    · exact hArcH j
    · exact hArcT j
  · intro i j hij
    exact (arc_inter_of_ne (frontier C) hij).trans haxis
  · intro i
    exact hRegion i.1 i.2

end Geometry.SimplicialComplex
