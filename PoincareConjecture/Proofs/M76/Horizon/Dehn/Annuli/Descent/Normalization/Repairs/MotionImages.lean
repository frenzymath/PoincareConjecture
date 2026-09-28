import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Repairs.BranchMotion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchInnerSupport










set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.AnnulusBranchMotion

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}
  {D : OriginalRelativeNormalization step K j R Rim}
  {a b : K.space} {W : Set s.Carrier} {ε : ℝ}
  (N : AnnulusBranchMotion D a b W ε)

theorem support_branch_target : N.support.space ⊆ (N.window.right.trans N.chart).target := by
  intro z hz
  exact ⟨N.support_target hz, N.window.right_target.symm.subset
    ((N.chart_inside (N.chart.map_target (N.support_target hz))).2.2)⟩

theorem right_source_preserved (u : I) (x : t.Carrier) :
    N.ambient u x ∈ (N.window.right.trans N.chart).source ↔
      x ∈ (N.window.right.trans N.chart).source := by
  let B := N.window.right.trans N.chart
  have hout (y : t.Carrier) (hy : y ∉ B.source) : N.ambient u y = y := by
    apply N.outside u
    rintro ⟨z, hz, rfl⟩
    exact hy (B.map_target (N.support_branch_target hz))
  constructor
  · intro hx
    by_contra hn
    exact hn (hout x hn ▸ hx)
  · intro hx
    by_contra hn
    have heq : N.ambient u x = x := (N.ambient u).injective (hout (N.ambient u x) hn)
    exact hn (heq.symm ▸ hx)

theorem right_coordinate_value (u : I) {x : t.Carrier}
    (hx : x ∈ (N.window.right.trans N.chart).source) :
    (N.window.right.trans N.chart) (N.ambient u x) =
      N.motion.map u ((N.window.right.trans N.chart) x) := by
  let B := N.window.right.trans N.chart
  rw [N.formula u hx]
  change B (B.symm (N.motion.map u (B x))) = N.motion.map u (B x)
  apply B.right_inv
  by_cases hz : B x ∈ N.support.space
  · exact N.support_branch_target ((N.motion.carrier u).subset
      (mem_image_of_mem (N.motion.map u) hz))
  · rw [N.motion.outside u (B x) (fun h ↦ hz (interior_subset h))]
    exact B.map_source hx

theorem moved_right_image :
    (N.window.right.trans N.chart) ''
      ((N.ambient 1 ∘ D.endpoint) '' K.space ∩ (N.window.right.trans N.chart).source) ∩
        N.support.space = N.movedBranch.space := by
  let B := N.window.right.trans N.chart
  have hJiff (z : V3) : N.motion.map 1 z ∈ N.support.space ↔ z ∈ N.support.space := by
    constructor
    · intro hz
      obtain ⟨y, hy, heq⟩ := (N.motion.carrier 1).symm.subset hz
      exact (N.motion.map 1).injective heq ▸ hy
    · intro hz
      exact (N.motion.carrier 1).subset (mem_image_of_mem (N.motion.map 1) hz)
  rw [N.moved_space]
  apply Subset.antisymm
  · rintro z ⟨⟨y, ⟨⟨x, hx, hxy⟩, hyB⟩, hyz⟩, hzJ⟩
    have hxy' : N.ambient 1 (D.endpoint x) = y := hxy
    have hxB : D.endpoint x ∈ B.source :=
      (N.right_source_preserved 1 _).mp (hxy'.symm ▸ hyB)
    have heq : N.motion.map 1 (B (D.endpoint x)) = z :=
      (N.right_coordinate_value 1 hxB).symm.trans ((congrArg B hxy).trans hyz)
    refine ⟨B (D.endpoint x), N.source_space.symm.subset ?_, heq⟩
    exact ⟨⟨D.endpoint x, ⟨mem_image_of_mem _ hx, hxB⟩, rfl⟩,
      (hJiff _).mp (heq.symm ▸ hzJ)⟩
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨⟨v, ⟨⟨x, hx, hxv⟩, hvB⟩, hvy⟩, hyJ⟩ := N.source_space.subset hy
    have hxB : D.endpoint x ∈ B.source := hxv.symm ▸ hvB
    have hxy : B (D.endpoint x) = y := (congrArg B hxv).trans hvy
    refine ⟨⟨N.ambient 1 (D.endpoint x),
      ⟨⟨x, hx, rfl⟩, (N.right_source_preserved 1 _).mpr hxB⟩, ?_⟩, (hJiff _).mpr hyJ⟩
    rw [N.right_coordinate_value 1 hxB, hxy]

theorem moved_left_image (u : I) :
    (N.ambient u ∘ D.endpoint) '' K.space ∩ N.window.left.source =
      D.endpoint '' K.space ∩ N.window.left.source := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hxl⟩
    have heq : D.endpoint y = x := (N.ambient u).injective
      (hyx.trans (N.left_fixed u hxl).symm)
    exact ⟨⟨y, hy, heq⟩, hxl⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyl⟩
    exact ⟨⟨y, hy, N.left_fixed u hyl⟩, hyl⟩



theorem endpoint_properties (hK : K.faces.Finite) :
    PolyhedralPLInCharts t.charts (N.ambient 1 ∘ D.endpoint) K.space ∧
      IsEmbedding (fun x : K.space ↦ N.ambient 1 (D.endpoint x)) ∧
      MapsTo (N.ambient 1 ∘ D.endpoint) K.space (t.projection ⁻¹' R) ∧
      (∀ x ∈ K.space, N.ambient 1 (D.endpoint x) ∈ frontier (t.projection ⁻¹' R) ↔
        x ∈ Rim) ∧ EqOn (N.ambient 1 ∘ D.endpoint) j Rim := by
  have hproper (x : A) (hx : x ∈ K.space) :
      D.endpoint x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Rim :=
    (D.states D.length).proper x (D.subdivision.space_eq.symm.subset hx)
  refine ⟨D.endpoint_PL.comp_chart_homeomorph K hK (N.ambient 1) t.cover (N.ambient_PL 1),
    (N.ambient 1).isEmbedding.comp D.endpoint_embedding, ?_, ?_, ?_⟩
  · intro x hx
    change D.endpoint x ∈ (N.ambient 1) ⁻¹' (t.projection ⁻¹' R)
    rw [N.region]
    exact (D.states D.length).region (D.subdivision.space_eq.symm.subset hx)
  · intro x hx
    have hfront : (N.ambient 1) ⁻¹' frontier (t.projection ⁻¹' R) =
        frontier (t.projection ⁻¹' R) := by
      rw [(N.ambient 1).preimage_frontier, N.region]
    exact (Set.ext_iff.mp hfront (D.endpoint x)).trans (hproper x hx)
  · intro x hx
    have hxK := D.subdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le D.protected_le (D.boundary_protected hx))
    exact (N.frontier_fixed 1 ((hproper x hxK).mpr hx)).trans (D.endpoint_boundary hx)



theorem compact_change_support :
    ∃ Small : Set t.Carrier, IsCompact Small ∧
      IsCompact (Small ∪ N.ambient 1 '' Small) ∧
      Small ∪ N.ambient 1 '' Small ⊆
        (N.window.right.trans N.chart).symm '' interior N.support.space ∧
      Small ∪ N.ambient 1 '' Small ⊆
        (step.projection ∘ step.inclusion) ⁻¹' W ∧
      D.projected a ∈ (step.projection ∘ step.inclusion) '' Small ∧
      ∀ u, EqOn (N.ambient u) id (D.endpoint '' K.space \ Small) := by
  let B := N.window.right.trans N.chart
  let Small := B.symm '' closedBall (0 : V3) N.radius
  obtain ⟨hS, hSnew, hSJ, hfix⟩ := branch_disk_change_support_with_endpoint B
    (D.endpoint '' K.space) N.support.space N.source.space N.fixed.space N.radius
    N.closed_clearance N.support_branch_target N.source_space N.fixed_space
    N.motion N.ambient N.formula N.outside N.protected_fixed
  refine ⟨Small, hS, hSnew, hSJ, ?_, ?_, hfix⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hSJ hx
    have hzB := N.support_branch_target (interior_subset hz)
    have hsource := B.map_target hzB
    have hcoord : N.window.right (B.symm z) ∈ N.chart.source := hsource.2
    rw [N.window.right_eq] at hcoord
    exact (N.chart_inside hcoord).1
  · have h0J : (0 : V3) ∈ N.support.space := interior_subset N.center_interior
    have h0B := N.support_branch_target h0J
    refine ⟨B.symm 0, ⟨0, ?_, rfl⟩, ?_⟩
    · simpa only [mem_closedBall, dist_self] using N.radius_pos.le
    · change (step.projection ∘ step.inclusion) (N.window.right.symm (N.chart.symm 0)) =
        D.projected a
      exact (congrFun N.window.right_eq _).symm.trans
        ((N.window.right.right_inv h0B.2).trans
          ((congrArg N.chart.symm N.centered).symm.trans (N.chart.left_inv N.point)))

end Geometry.OriginalPLTower.AnnulusBranchMotion
