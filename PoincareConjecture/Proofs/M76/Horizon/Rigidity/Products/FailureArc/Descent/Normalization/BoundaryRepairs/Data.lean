import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.ProjectedBranches
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartRegion
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgery











set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}


structure PlanarAnnulusBoundaryMotion
    (step : Step s t) (j : P2 → t.Carrier) (R Fmark : Set M)
    (a b : Ann) (W : Set s.Carrier) (ε : ℝ) where
  window : TwoBranchWindow (step.projection ∘ step.inclusion)
  coordinates : V3 ≃L[ℝ] C3
  chart : OpenPartialHomeomorph s.Carrier V3
  left_point : j a ∈ window.left.source
  right_point : j b ∈ window.right.source
  point : step.projection (step.inclusion (j a)) ∈ chart.source
  centered : chart (step.projection (step.inclusion (j a))) = 0
  chart_inside : chart.source ⊆ W ∩ window.target
  lower_PL : ∀ k, (s.charts k).symm.trans chart ∈ piecewiseAffineGroupoid V3
  branches_PL : ∀ k,
    (t.charts k).symm.trans (window.left.trans chart) ∈ piecewiseAffineGroupoid V3 ∧
    (t.charts k).symm.trans (window.right.trans chart) ∈ piecewiseAffineGroupoid V3
  lower_region : ∀ y ∈ chart.source,
    y ∈ s.projection ⁻¹' R ↔ 0 ≤ (coordinates (chart y)).1.1
  lower_frontier : ∀ y ∈ chart.source,
    y ∈ frontier (s.projection ⁻¹' R) ↔ (coordinates (chart y)).1.1 = 0
  lower_mark : ∀ y ∈ chart.source,
    s.projection y ∈ Fmark ↔ (coordinates (chart y)).1.1 = 0
  left_halfplane : ∀ y ∈ chart.source,
    y ∈ (step.projection ∘ step.inclusion) '' (j '' Ann ∩ window.left.source) ↔
      0 ≤ (coordinates (chart y)).1.1 ∧ (coordinates (chart y)).2 = 0
  support : SimplicialComplex ℝ V3
  source : SimplicialComplex ℝ V3
  boundary : SimplicialComplex ℝ V3
  fixed : SimplicialComplex ℝ V3
  ambientComplex : SimplicialComplex ℝ V3
  branchComplex : SimplicialComplex ℝ V3
  rimComplex : SimplicialComplex ℝ V3
  fixedRim : SimplicialComplex ℝ V3
  line : SimplicialComplex ℝ V3
  parameter : V3 → P2
  radius : ℝ
  radius_pos : 0 < radius
  support_finite : support.faces.Finite
  support_convex : Convex ℝ support.space
  support_target : support.space ⊆ chart.target
  center_interior : (0 : V3) ∈ interior support.space
  closed_clearance : closedBall (0 : V3) radius ⊆ interior support.space
  source_finite : source.faces.Finite
  source_space : source.space = (window.right.trans chart) ''
    (j '' Ann ∩ (window.right.trans chart).source) ∩ support.space
  center_source : (0 : V3) ∈ source.space
  boundary_finite : boundary.faces.Finite
  boundary_level : boundary.space = source.space ∩ {z | (coordinates z).1.1 = 0}
  boundary_space : boundary.space = (window.right.trans chart) ''
    (j '' Rim ∩ (window.right.trans chart).source) ∩ support.space
  fixed_finite : fixed.faces.Finite
  fixed_space : fixed.space = source.space \ ball (0 : V3) radius
  parameter_PL : FinitePiecewiseAffineOn parameter source.space
  parameter_injective : InjOn parameter source.space
  parameter_range : MapsTo parameter source.space Ann
  parameter_right : ∀ z ∈ source.space,
    j (parameter z) ∈ (window.right.trans chart).source ∧
      (window.right.trans chart) (j (parameter z)) = z
  parameter_left : ∀ z ∈ Ann, j z ∈ (window.right.trans chart).source →
    (window.right.trans chart) (j z) ∈ support.space →
      parameter ((window.right.trans chart) (j z)) = z
  parameter_rim : ∀ z ∈ source.space, z ∈ boundary.space ↔ parameter z ∈ Rim
  parameter_interior : ∀ z ∈ source.space, z ∈ interior support.space →
    parameter z ∈ interior Ann → parameter z ∈ interior (parameter '' source.space)
  ambient_finite : ambientComplex.faces.Finite
  subdivision : ambientComplex.IsSubdivision support
  branch_le : branchComplex ≤ ambientComplex
  branch_space : branchComplex.space = source.space
  parameter_affine : branchComplex.AffineOnFaces parameter
  rim_le : rimComplex ≤ branchComplex
  rim_space : rimComplex.space = boundary.space
  fixed_le : fixedRim ≤ rimComplex
  fixed_rim_space : fixedRim.space = boundary.space ∩ (fixed.space ∪ frontier support.space)
  fixed_full : ∀ face ∈ rimComplex.faces,
    (∀ v ∈ face, v ∈ fixedRim.vertices) → face ∈ fixedRim.faces
  line_finite : line.faces.Finite
  line_space : line.space = support.space ∩
    {z | (coordinates z).1.1 = 0 ∧ (coordinates z).2 = 0}
  motion : PLCarrierMotion support.space fixed.space ε
  endpoint_affine : ambientComplex.AffineOnFaces (motion.map 1)
  height : ∀ u z, (coordinates (motion.map u z)).1.1 = (coordinates z).1.1
  signs : ∀ v ∈ ambientComplex.vertices, (coordinates v).2 ≠ 0 → ∀ u,
    (0 < (coordinates (motion.map u v)).2 ↔ 0 < (coordinates v).2) ∧
      ((coordinates (motion.map u v)).2 < 0 ↔ (coordinates v).2 < 0)
  zero_vertices : ∀ v ∈ rimComplex.vertices,
    (coordinates (motion.map 1 v)).2 = 0 ↔
      v ∈ fixedRim.vertices ∧ (coordinates v).2 = 0
  zero_faces : ∀ face ∈ rimComplex.faces,
    (∀ v ∈ face, (coordinates (motion.map 1 v)).2 = 0) ↔
      face ∈ fixedRim.faces ∧ ∀ v ∈ face, (coordinates v).2 = 0
  branch_zero_faces : ∀ face ∈ branchComplex.faces,
    (∀ v ∈ face, (coordinates (motion.map 1 v)).2 = 0) →
      ∀ v ∈ face, (coordinates v).2 = 0
  position : ∀ face ∈ rimComplex.faces, face ∉ fixedRim.faces →
    ∀ other ∈ line.faces,
      affineSpan ℝ (motion.map 1 '' (face : Set V3) ∪ (other : Set V3)) =
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp
            coordinates.toContinuousLinearMap)).ker.toAffineSubspace ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (motion.map 1 '' (face : Set V3))))
          (convexHull ℝ (other : Set V3))
  ambient : I → t.Carrier ≃ₜ t.Carrier
  continuous : Continuous (fun z : I × t.Carrier => ambient z.1 z.2)
  continuous_inverse : Continuous (fun z : I × t.Carrier => (ambient z.1).symm z.2)
  zero : ∀ x, ambient 0 x = x
  formula : ∀ u, EqOn (ambient u)
    ((window.right.trans chart).symm ∘ motion.map u ∘ (window.right.trans chart))
    (window.right.trans chart).source
  outside : ∀ u, EqOn (ambient u) id ((window.right.trans chart).symm '' support.space)ᶜ
  protected_fixed : ∀ u, EqOn (ambient u) id ((window.right.trans chart).symm '' fixed.space)
  left_fixed : ∀ u, EqOn (ambient u) id window.left.source
  region : ∀ u, (ambient u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  frontier : ∀ u, (ambient u) ⁻¹' frontier (t.projection ⁻¹' R) = frontier (t.projection ⁻¹' R)
  mark : ∀ u, (ambient u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark
  ambient_PL : ∀ u k l, (t.charts k).symm.trans
    ((ambient u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3
  inverse_PL : ∀ u k l, (t.charts k).symm.trans
    ((ambient u).symm.toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3

end Geometry.OriginalPLTower
