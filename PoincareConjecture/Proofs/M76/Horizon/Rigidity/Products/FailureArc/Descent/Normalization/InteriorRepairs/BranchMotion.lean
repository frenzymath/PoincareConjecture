import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.PlanarBranchCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Repairs.CoordinateSupport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierInteriorChartMotion

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}

structure PlanarSurfaceBranchMotion
    (step : Step s t) (K : SimplicialComplex ℝ A) (j : A → t.Carrier) (R : Set M)
    (a b : K.space) (W : Set s.Carrier) (ε : ℝ) where
  window : TwoBranchWindow (step.projection ∘ step.inclusion)
  coordinates : V3 ≃L[ℝ] C3
  chart : OpenPartialHomeomorph s.Carrier V3
  left_point : j a ∈ window.left.source
  right_point : j b ∈ window.right.source
  point : (step.projection ∘ step.inclusion ∘ j) a ∈ chart.source
  centered : chart ((step.projection ∘ step.inclusion ∘ j) a) = 0
  chart_inside : chart.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ window.target)
  lower_PL : ∀ k, (s.charts k).symm.trans chart ∈ piecewiseAffineGroupoid V3
  branches_PL : ∀ k,
    (t.charts k).symm.trans (window.left.trans chart) ∈ piecewiseAffineGroupoid V3 ∧
    (t.charts k).symm.trans (window.right.trans chart) ∈ piecewiseAffineGroupoid V3
  left_plane : ∀ y ∈ chart.source, y ∈ (step.projection ∘ step.inclusion) ''
    (j '' K.space ∩ window.left.source) ↔ (coordinates (chart y)).2 = 0
  support : SimplicialComplex ℝ V3
  source : SimplicialComplex ℝ V3
  fixed : SimplicialComplex ℝ V3
  ambientComplex : SimplicialComplex ℝ V3
  branchComplex : SimplicialComplex ℝ V3
  fixedComplex : SimplicialComplex ℝ V3
  plane : SimplicialComplex ℝ V3
  parameter : V3 → ℝ × ℝ
  radius : ℝ
  radius_pos : 0 < radius
  support_finite : support.faces.Finite
  support_convex : Convex ℝ support.space
  support_target : support.space ⊆ chart.target
  center_interior : (0 : V3) ∈ interior support.space
  closed_clearance : closedBall (0 : V3) radius ⊆ interior support.space
  source_finite : source.faces.Finite
  source_space : source.space = (window.right.trans chart) ''
    (j '' K.space ∩ (window.right.trans chart).source) ∩ support.space
  center_source : (0 : V3) ∈ source.space
  fixed_finite : fixed.faces.Finite
  fixed_space : fixed.space = source.space \ ball (0 : V3) radius
  parameter_PL : FinitePiecewiseAffineOn parameter source.space
  parameter_injective : InjOn parameter source.space
  parameter_interior : ∀ z ∈ source.space, z ∈ interior support.space →
    parameter z ∈ interior (parameter '' source.space)
  ambient_finite : ambientComplex.faces.Finite
  subdivision : ambientComplex.IsSubdivision support
  branch_le : branchComplex ≤ ambientComplex
  branch_space : branchComplex.space = source.space
  parameter_affine : branchComplex.AffineOnFaces parameter
  fixed_le : fixedComplex ≤ branchComplex
  fixed_carrier : fixedComplex.space = fixed.space
  fixed_full : ∀ face ∈ branchComplex.faces,
    (∀ v ∈ face, v ∈ fixedComplex.vertices) → face ∈ fixedComplex.faces
  plane_finite : plane.faces.Finite
  plane_space : plane.space = support.space ∩ {z | (coordinates z).2 = 0}
  old_links : ∀ v ∈ branchComplex.vertices, v ∈ interior support.space →
    ∃ (n : ℕ) (P : Polygon V3 (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (branchComplex.link v).space
  motion : PLCarrierMotion support.space fixed.space ε
  endpoint_affine : ambientComplex.AffineOnFaces (motion.map 1)
  signs : ∀ v ∈ ambientComplex.vertices, (coordinates v).2 ≠ 0 → ∀ u,
    (0 < (coordinates (motion.map u v)).2 ↔ 0 < (coordinates v).2) ∧
      ((coordinates (motion.map u v)).2 < 0 ↔ (coordinates v).2 < 0)
  zero_vertices : ∀ v ∈ branchComplex.vertices,
    (coordinates (motion.map 1 v)).2 = 0 ↔
      v ∈ fixedComplex.vertices ∧ (coordinates v).2 = 0
  zero_faces : ∀ face ∈ branchComplex.faces,
    (∀ v ∈ face, (coordinates (motion.map 1 v)).2 = 0) ↔
      face ∈ fixedComplex.faces ∧ ∀ v ∈ face, (coordinates v).2 = 0
  position : ∀ face ∈ branchComplex.faces, face ∉ fixedComplex.faces →
    ∀ other ∈ plane.faces,
      affineSpan ℝ (motion.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (motion.map 1 '' (face : Set V3))))
          (convexHull ℝ (other : Set V3))
  movedAmbient : SimplicialComplex ℝ V3
  movedBranch : SimplicialComplex ℝ V3
  moved_finite : movedAmbient.faces.Finite
  moved_ambient_space : movedAmbient.space = support.space
  moved_le : movedBranch ≤ movedAmbient
  moved_space : movedBranch.space = motion.map 1 '' source.space
  fixed_moved : fixedComplex ≤ movedBranch
  moved_parameter_affine : movedBranch.AffineOnFaces (parameter ∘ (motion.map 1).symm)
  moved_parameter_injective : InjOn (parameter ∘ (motion.map 1).symm) movedBranch.space
  moved_stars : ∀ v ∈ branchComplex.vertices,
    (movedBranch.link (motion.map 1 v)).space = motion.map 1 '' (branchComplex.link v).space ∧
    (movedBranch.closedStar (motion.map 1 v)).space =
      motion.map 1 '' (branchComplex.closedStar v).space
  moved_links : ∀ v ∈ branchComplex.vertices, v ∈ interior support.space →
    ∃ (n : ℕ) (P : Polygon V3 (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (movedBranch.link (motion.map 1 v)).space
  ambient : I → t.Carrier ≃ₜ t.Carrier
  continuous : Continuous (fun z : I × t.Carrier ↦ ambient z.1 z.2)
  continuous_inverse : Continuous (fun z : I × t.Carrier ↦ (ambient z.1).symm z.2)
  zero : ∀ x, ambient 0 x = x
  formula : ∀ u, EqOn (ambient u)
    ((window.right.trans chart).symm ∘ motion.map u ∘ (window.right.trans chart))
    (window.right.trans chart).source
  outside : ∀ u, EqOn (ambient u) id ((window.right.trans chart).symm '' support.space)ᶜ
  protected_fixed : ∀ u, EqOn (ambient u) id ((window.right.trans chart).symm '' fixed.space)
  left_fixed : ∀ u, EqOn (ambient u) id window.left.source
  frontier_fixed : ∀ u, EqOn (ambient u) id (frontier (t.projection ⁻¹' R))
  region : ∀ u, (ambient u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  ambient_PL : ∀ u k l, (t.charts k).symm.trans
    ((ambient u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3
  inverse_PL : ∀ u k l, (t.charts k).symm.trans
    ((ambient u).symm.toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3

theorem Step.nonempty_planar_surface_branch_motion
    (step : Step s t) (hK : K.faces.Finite)
    (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space => j x))
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ frontier K.space)
    (a b : K.space) (hab : a ≠ b) (hpair : (step.projection ∘ step.inclusion ∘ j) a = (step.projection ∘ step.inclusion ∘ j) b)
    (haint : (step.projection ∘ step.inclusion ∘ j) a ∈ interior (s.projection ⁻¹' R))
    {W : Set s.Carrier} (hW : IsOpen W) (haW : (step.projection ∘ step.inclusion ∘ j) a ∈ W)
    (ε : ℝ) (hε : 0 < ε) : Nonempty (PlanarSurfaceBranchMotion step K j R a b W ε) := by
  classical
  obtain ⟨w, c, Q, hal, hbr, haQ, hQzero, hQW, hQPL, hbranches, _, hplane, hclip⟩ :=
    step.exists_planar_surface_parameterized_branch_chart hK hj hji hproper a b hab hpair haint hW haW
  have hzeroQ : (0 : V3) ∈ Q.target := hQzero ▸ Q.map_source haQ
  obtain ⟨r₀, J, hr₀, hJ, hJs, hJQ, _, _⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target hzeroQ
  have hcv : Convex ℝ J.space := hJs.symm ▸ convex_closedBall (0 : V3) (3 * r₀)
  have hzeroJ : (0 : V3) ∈ interior J.space := by
    rw [hJs]
    apply ball_subset_interior_closedBall
    simpa only [mem_ball, dist_self] using (show 0 < 3 * r₀ by positivity)
  obtain ⟨P, g, q₀, hP, hPs, _, _, _, _, hq₀, hq₀i, hq₀int⟩ := hclip J hJ hJQ
  obtain ⟨ρ, P₀, hρ, hclosed, hP₀, hP₀s, hfront⟩ :=
    exists_finite_branch_outer_collar J P hP hzeroJ
  have hP₀P : P₀.space ⊆ P.space := hP₀s.subset.trans sdiff_subset
  have hPJ : P.space ⊆ J.space := hPs.subset.trans inter_subset_right
  let q : V3 → ℝ × ℝ := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) ∘ q₀
  have hq : FinitePiecewiseAffineOn q P.space :=
    hq₀.postcomp (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap
  have hqi : InjOn q P.space := fun x hx y hy h ↦
    hq₀i hx hy ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).injective h)
  have hqint (z : V3) (hz : z ∈ P.space) (hzJ : z ∈ interior J.space) :
      q z ∈ interior (q '' P.space) := by
    let E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph
    change E (q₀ z) ∈ interior ((E ∘ q₀) '' P.space)
    exact interior_mono (image_image E q₀ P.space).subset
      ((E.image_interior _).subset (mem_image_of_mem E (hq₀int z hz hzJ)))
  let B := w.right.trans Q
  have hJB : J.space ⊆ B.target := by
    intro z hz
    exact ⟨hJQ hz, w.right_target.symm.subset ((hQW (Q.map_target (hJQ hz))).2.2)⟩
  have hbB : j b ∈ B.source := by
    refine ⟨hbr, ?_⟩
    change w.right (j b) ∈ Q.source
    rw [w.right_eq]
    change (step.projection ∘ step.inclusion ∘ j) b ∈ Q.source
    rw [← hpair]
    exact haQ
  have hzeroP : (0 : V3) ∈ P.space := by
    apply hPs.symm.subset
    refine ⟨⟨j b, ⟨mem_image_of_mem _ b.property, hbB⟩, ?_⟩,
      interior_subset hzeroJ⟩
    change Q (w.right (j b)) = 0
    rw [w.right_eq]
    change Q ((step.projection ∘ step.inclusion ∘ j) b) = 0
    rw [← hpair, hQzero]
  let ell : V3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hell : ell ≠ 0 := by
    intro h
    have hv : ell (c.symm ((0, 0), 1)) = 1 := by
      change (c (c.symm ((0, 0), 1))).2 = 1
      rw [c.apply_symm_apply]
    rw [h, zero_apply] at hv
    exact zero_ne_one hv
  obtain ⟨T, L, L₀, plane, hT, hTJ, hLT, hLs, hqL, hL₀L, hL₀s, hfull,
    hplaneFin, hplaneSpace, hlinks, δ, _, _, hmotions⟩ :=
    exists_parameterized_protected_branch_repair J P P₀ hJ hP hP₀ hcv hP₀P hPJ
      hfront q hq hqi ell hell
  obtain ⟨H, hHaff, hsign, hzero, hfaces, hposition,
    T', L', hT', hT's, hL'T', hL's, hL₀L', hqL', hqiL', hstars, hlinks'⟩ := hmotions ε hε
  have hBinside : B.source ⊆ interior (t.projection ⁻¹' R) := by
    intro x hx
    have hxp : (step.projection ∘ step.inclusion) x ∈ Q.source :=
      (congrFun w.right_eq x) ▸ hx.2
    have h := preimage_interior_subset_interior_preimage
      (step.projection.continuous.comp step.inclusion.continuous) (hQW hxp).2.1
    exact interior_mono (step.region_preimage R).symm.subset h
  obtain ⟨G, hG, hGi, hGzero, hformula, hout, hfixed, _, _, hfrontier,
    hregion, hGPL, hGiPL⟩ := H.exists_interior_chart_motion J hJ B.symm hJB
      (hP₀P.trans (hPJ.trans hJB)) t.charts t.compatible (fun k ↦ (hbranches k).2)
      (R := t.projection ⁻¹' R) (F := ∅) (empty_subset _) (Or.inl hBinside)
  have hleft (u : I) : EqOn (G u) id w.left.source := by
    intro x hx
    apply hout u
    rintro ⟨z, hz, rfl⟩
    exact disjoint_left.mp w.disjoint hx (B.map_target (hJB hz)).1
  exact ⟨{
    window := w, coordinates := c, chart := Q
    left_point := hal, right_point := hbr, point := haQ, centered := hQzero
    chart_inside := hQW, lower_PL := hQPL, branches_PL := hbranches, left_plane := hplane
    support := J, source := P, fixed := P₀, ambientComplex := T
    branchComplex := L, fixedComplex := L₀, plane := plane, parameter := q
    radius := ρ, radius_pos := hρ, support_finite := hJ, support_convex := hcv
    support_target := hJQ, center_interior := hzeroJ, closed_clearance := hclosed
    source_finite := hP, source_space := hPs, center_source := hzeroP
    fixed_finite := hP₀, fixed_space := hP₀s
    parameter_PL := hq, parameter_injective := hqi, parameter_interior := hqint
    ambient_finite := hT, subdivision := hTJ, branch_le := hLT, branch_space := hLs
    parameter_affine := hqL, fixed_le := hL₀L, fixed_carrier := hL₀s, fixed_full := hfull
    plane_finite := hplaneFin, plane_space := hplaneSpace
    old_links := fun v hv hi ↦ hlinks v hv (hqint v (hLs.subset (L.vertices_subset_space hv)) hi)
    motion := H, endpoint_affine := hHaff
    signs := fun v hv hn u ↦ (hsign v hv hn u).2
    zero_vertices := hzero, zero_faces := hfaces, position := hposition
    movedAmbient := T', movedBranch := L', moved_finite := hT', moved_ambient_space := hT's
    moved_le := hL'T', moved_space := hL's, fixed_moved := hL₀L'
    moved_parameter_affine := hqL', moved_parameter_injective := hqiL', moved_stars := hstars
    moved_links := fun v hv hi ↦ hlinks' v hv (hqint v (hLs.subset (L.vertices_subset_space hv)) hi)
    ambient := G, continuous := hG, continuous_inverse := hGi, zero := hGzero
    formula := hformula, outside := hout, protected_fixed := hfixed, left_fixed := hleft
    frontier_fixed := hfrontier, region := fun u ↦ (hregion u).1
    ambient_PL := hGPL, inverse_PL := hGiPL }⟩

end Geometry.OriginalPLTower
