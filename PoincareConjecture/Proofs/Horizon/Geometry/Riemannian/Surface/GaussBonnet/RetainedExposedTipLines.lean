import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.AffineRaySectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

theorem two_positive_rays_eq_affine_line_of_not_independent
    (a : Plane) (d : Bool → Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (ha : l a = 0)
    (hd : ∀ j, d j ≠ 0) (hld : l.linear (d false) = 0)
    (hpos : ∀ c : ℝ, 0 < c → d true ≠ c • d false)
    (hind : ¬ LinearIndependent ℝ (![d false, d true] : Fin 2 → Plane)) :
    (⋃ j : Bool, (fun t : ℝ => a + t • d j) '' Ici (0 : ℝ)) = {z | l z = 0} := by
  obtain ⟨c, hc, he⟩ :=
    (independent_or_negative_smul_of_not_pos_smul (hd false) (hd true) hpos).resolve_left hind
  have hu : (⋃ j : Bool, (fun t : ℝ => a + t • d j) '' Ici (0 : ℝ)) =
      ((fun t : ℝ => a + t • d false) '' Ici (0 : ℝ)) ∪
        ((fun t : ℝ => a + t • d true) '' Ici (0 : ℝ)) := by
    ext z
    constructor
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      cases j
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (h | h)
      · exact mem_iUnion.mpr ⟨false, h⟩
      · exact mem_iUnion.mpr ⟨true, h⟩
  rw [hu, he, union_opposite_positive_rays_eq_range a (d false) hc]
  exact affine_ray_range_eq_zero_set l hl ha (hd false) hld

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

omit [T2Space S] in
theorem chordSupportingLine_outer_tips (i j : Bool) :
    B.chordSupportingLine (i, j) (chartAt Plane (x (i, j)) (B.firstOuterTip i)) = 0 ∧
      B.chordSupportingLine (i, j) (chartAt Plane (x (i, j)) (B.secondOuterTip j)) = 0 := by
  have h₁ := (B.chordSupportingLine_spec (i, j)).2
    (left_mem_affineSegment ℝ
      (chartAt Plane (x (i, j)) (P.sectorCoordinates (i, j) (B.scale, 0)))
      (chartAt Plane (x (i, j)) (P.sectorCoordinates (i, j) (0, B.scale))))
  have h₂ := (B.chordSupportingLine_spec (i, j)).2
    (right_mem_affineSegment ℝ
      (chartAt Plane (x (i, j)) (P.sectorCoordinates (i, j) (B.scale, 0)))
      (chartAt Plane (x (i, j)) (P.sectorCoordinates (i, j) (0, B.scale))))
  constructor
  · simpa only [mem_ofPred_eq, B.sector_first_tip_eq] using h₁
  · simpa only [mem_ofPred_eq, B.sector_second_tip_eq] using h₂

theorem first_outer_rays_eq_line_of_not_independent (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane v (B.secondOuterTip false) - chartAt Plane v (B.firstOuterTip i),
        chartAt Plane v (B.secondOuterTip true) - chartAt Plane v (B.firstOuterTip i)] :
          Fin 2 → Plane)) :
    (⋃ j : Bool, (fun t : ℝ => chartAt Plane v (B.firstOuterTip i) + t •
      (chartAt Plane v (B.secondOuterTip j) - chartAt Plane v (B.firstOuterTip i))) ''
        Ici (0 : ℝ)) = {z | B.chordSupportingLine (i, false) z = 0} := by
  let F := chartAt Plane v
  let l := B.chordSupportingLine (i, false)
  have he := B.chordSupportingLine_outer_tips i false
  rw [hchart false] at he
  apply two_positive_rays_eq_affine_line_of_not_independent
    (F (B.firstOuterTip i)) (fun j => F (B.secondOuterTip j) - F (B.firstOuterTip i)) l
    (B.chordSupportingLine_spec (i, false)).1 he.1 _ _
    (fun c hc => B.first_outer_chords_not_pos_smul i v hchart hc) hind
  · intro j
    have h := B.chord_chart_endpoints_ne (i, j)
    simp only [hchart, B.sector_first_tip_eq, B.sector_second_tip_eq] at h
    exact sub_ne_zero.mpr (Ne.symm h)
  · change l.linear (F (B.secondOuterTip false) -ᵥ F (B.firstOuterTip i)) = 0
    rw [l.linearMap_vsub, vsub_eq_sub, he.1, he.2, sub_self]

theorem second_outer_rays_eq_line_of_not_independent (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane v (B.firstOuterTip false) - chartAt Plane v (B.secondOuterTip i),
        chartAt Plane v (B.firstOuterTip true) - chartAt Plane v (B.secondOuterTip i)] :
          Fin 2 → Plane)) :
    (⋃ j : Bool, (fun t : ℝ => chartAt Plane v (B.secondOuterTip i) + t •
      (chartAt Plane v (B.firstOuterTip j) - chartAt Plane v (B.secondOuterTip i))) ''
        Ici (0 : ℝ)) = {z | B.chordSupportingLine (false, i) z = 0} := by
  let F := chartAt Plane v
  let l := B.chordSupportingLine (false, i)
  have he := B.chordSupportingLine_outer_tips false i
  rw [hchart false] at he
  apply two_positive_rays_eq_affine_line_of_not_independent
    (F (B.secondOuterTip i)) (fun j => F (B.firstOuterTip j) - F (B.secondOuterTip i)) l
    (B.chordSupportingLine_spec (false, i)).1 he.2 _ _
    (fun c hc => B.second_outer_chords_not_pos_smul i v hchart hc) hind
  · intro j
    have h := B.chord_chart_endpoints_ne (j, i)
    simp only [hchart, B.sector_first_tip_eq, B.sector_second_tip_eq] at h
    exact sub_ne_zero.mpr h
  · change l.linear (F (B.firstOuterTip false) -ᵥ F (B.secondOuterTip i)) = 0
    rw [l.linearMap_vsub, vsub_eq_sub, he.1, he.2, sub_self]

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in

theorem exists_core_halfspace_of_contact_line_frontier
    (R : T.decomposition.regions) {z : Plane}
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hmem : l ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R)
    (hlz : l z = 0)
    (hfront : frontier (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z] {w | l w = 0}) :
    ∃ m : Plane →ᵃ[ℝ] ℝ, Function.Surjective m ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ c : ℝ, c ≠ 0 ∧ m = c • k) ∧
      m z = 0 ∧ (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z] {w | 0 ≤ m w} := by
  rcases mesh_support_germ_of_affine_line (T.refined.mesh R) l hl hlz hfront with hp | hn
  · exact ⟨l, hl, ⟨l, hmem, 1, one_ne_zero, by simp⟩, hlz, hp⟩
  · refine ⟨-l, ?_, ⟨l, hmem, -1, neg_ne_zero.mpr one_ne_zero, by simp⟩, ?_, ?_⟩
    · intro y
      obtain ⟨w, hw⟩ := hl (-y)
      refine ⟨w, ?_⟩
      change -l w = y
      rw [hw, neg_neg]
    · change -l z = 0
      rw [hlz, neg_zero]
    · filter_upwards [hn] with w hw
      change (T.refined.mesh R).toPlaneComplex.support w = (0 ≤ -l w)
      change (T.refined.mesh R).toPlaneComplex.support w = (l w ≤ 0) at hw
      simpa only [neg_nonneg] using hw

theorem exists_core_halfspace_at_collinear_first_outer_tip
    (p : T.decomposition.vertices) (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true) - z] : Fin 2 → Plane)) :
    ∃ m : Plane →ᵃ[ℝ] ℝ, Function.Surjective m ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ c : ℝ, c ≠ 0 ∧ m = c • k) ∧
      m z = 0 ∧ (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z] {w | 0 ≤ m w} := by
  have hchart (j : Bool) : (T.chart (T.region p (i, j)) : S) = (T.chart R : S) := by
    rw [hregion (i, j) (((T.caps p).firstOuterTip_mem_carrier_iff i (i, j)).mpr rfl)]
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip i) = z := by
    rw [← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have hline := (T.caps p).first_outer_rays_eq_line_of_not_independent i
    (T.chart R : S) hchart (by simpa only [hp] using hind)
  rw [hp] at hline
  have hfront := T.core_frontier_first_outer_rays p R i hz hq hregion hband
  rw [hline] at hfront
  let l := (T.caps p).chordSupportingLine (i, false)
  have hlz := ((T.caps p).chordSupportingLine_outer_tips i false).1
  rw [hchart false, hp] at hlz
  apply T.exists_core_halfspace_of_contact_line_frontier R l
    ((T.caps p).chordSupportingLine_spec (i, false)).1 _ hlz hfront
  apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
  exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region
    (hregion (i, false) (((T.caps p).firstOuterTip_mem_carrier_iff i (i, false)).mpr rfl))

theorem exists_core_halfspace_at_collinear_second_outer_tip
    (p : T.decomposition.vertices) (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true) - z] : Fin 2 → Plane)) :
    ∃ m : Plane →ᵃ[ℝ] ℝ, Function.Surjective m ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ c : ℝ, c ≠ 0 ∧ m = c • k) ∧
      m z = 0 ∧ (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z] {w | 0 ≤ m w} := by
  have hchart (j : Bool) : (T.chart (T.region p (j, i)) : S) = (T.chart R : S) := by
    rw [hregion (j, i) (((T.caps p).secondOuterTip_mem_carrier_iff i (j, i)).mpr rfl)]
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip i) = z := by
    rw [← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have hline := (T.caps p).second_outer_rays_eq_line_of_not_independent i
    (T.chart R : S) hchart (by simpa only [hp] using hind)
  rw [hp] at hline
  have hfront := T.core_frontier_second_outer_rays p R i hz hq hregion hband
  rw [hline] at hfront
  let l := (T.caps p).chordSupportingLine (false, i)
  have hlz := ((T.caps p).chordSupportingLine_outer_tips false i).2
  rw [hchart false, hp] at hlz
  apply T.exists_core_halfspace_of_contact_line_frontier R l
    ((T.caps p).chordSupportingLine_spec (false, i)).1 _ hlz hfront
  apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
  exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region
    (hregion (false, i) (((T.caps p).secondOuterTip_mem_carrier_iff i (false, i)).mpr rfl))

theorem core_contribution_at_collinear_first_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hzq : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (htip : q.1 = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true) - z] : Fin 2 → Plane)) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q.1) = Real.pi := by
  obtain ⟨l, hl, hlines, hlz, hlocal⟩ :=
    T.exists_core_halfspace_at_collinear_first_outer_tip p R i hz
      (hzq.trans htip) hregion hband hind
  exact T.core_contribution_at_straight_canonical_vertex g R q hzq hz l hl hlines hlz hlocal

theorem core_contribution_at_collinear_second_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hzq : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (htip : q.1 = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true) - z] : Fin 2 → Plane)) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q.1) = Real.pi := by
  obtain ⟨l, hl, hlines, hlz, hlocal⟩ :=
    T.exists_core_halfspace_at_collinear_second_outer_tip p R i hz
      (hzq.trans htip) hregion hband hind
  exact T.core_contribution_at_straight_canonical_vertex g R q hzq hz l hl hlines hlz hlocal

end RetainedCoordinateTriangulation

end PoincareConjecture.Topology.Surface
