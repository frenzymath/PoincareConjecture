import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCoreSectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.AffineRaySectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapChordHalfspaces

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

theorem exists_affineBasis_of_independent_chord_vectors (z a b : Plane)
    (h : LinearIndependent ℝ (![a - z, b - z] : Fin 2 → Plane)) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane, c 0 = z ∧ c 1 = a ∧ c 2 = b := by
  have hi : AffineIndependent ℝ (![z, a, b] : Fin 3 → Plane) := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
    have he : ((fun i : {i : Fin 3 // i ≠ 0} =>
        (![z, a, b] : Fin 3 → Plane) i -ᵥ ![z, a, b] 0) ∘
        ⇑(finSuccAboveEquiv (0 : Fin 3))) = (![a - z, b - z] : Fin 2 → Plane) := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact h
  exact ⟨⟨![z, a, b], hi,
    hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane])⟩, rfl, rfl, rfl⟩

theorem affineBasis_first_coord_eq_smul_of_contact
    (c : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (h0 : l (c 0) = 0) (h2 : l (c 2) = 0) :
    ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • l := by
  apply affine_functionals_eq_smul_of_common_line l (c.coord 1) hl
  · intro t
    exact ⟨AffineMap.lineMap (c 0) (c 1) t,
      by simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]⟩
  · exact sub_ne_zero.mpr (c.ind.injective.ne (by decide : (2 : Fin 3) ≠ 0))
  · exact h0
  · simp
  · change l.linear (c 2 -ᵥ c 0) = 0
    rw [AffineMap.linearMap_vsub, h2, h0, vsub_self]
  · change (c.coord 1).linear (c 2 -ᵥ c 0) = 0
    rw [AffineMap.linearMap_vsub]
    norm_num [AffineBasis.coord_apply, Fin.ext_iff]

theorem affineBasis_second_coord_eq_smul_of_contact
    (c : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (h0 : l (c 0) = 0) (h1 : l (c 1) = 0) :
    ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • l := by
  apply affine_functionals_eq_smul_of_common_line l (c.coord 2) hl
  · intro t
    exact ⟨AffineMap.lineMap (c 0) (c 2) t,
      by simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]⟩
  · exact sub_ne_zero.mpr (c.ind.injective.ne (by decide : (1 : Fin 3) ≠ 0))
  · exact h0
  · simp
  · change l.linear (c 1 -ᵥ c 0) = 0
    rw [AffineMap.linearMap_vsub, h1, h0, vsub_self]
  · change (c.coord 2).linear (c 1 -ᵥ c 0) = 0
    rw [AffineMap.linearMap_vsub]
    norm_num [AffineBasis.coord_apply, Fin.ext_iff]

namespace RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in

theorem cap_contact_zero_at_outer_tips (p : T.decomposition.vertices)
    (s : Bool × Bool) (R : T.decomposition.regions) (hR : T.region p s = R) :
    (T.caps p).chordSupportingLine s
        (chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip s.1)) = 0 ∧
      (T.caps p).chordSupportingLine s
        (chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip s.2)) = 0 := by
  have h := ((T.caps p).chordSupportingLine_spec s).2
  rw [ChartCircleArrangementVertexPatch.VertexCapFaces.chartChord,
    (T.caps p).sector_first_tip_eq, (T.caps p).sector_second_tip_eq, hR] at h
  exact ⟨h (left_mem_affineSegment ℝ _ _), h (right_mem_affineSegment ℝ _ _)⟩

theorem first_outer_core_sector (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = z)
    (hc1 : c 1 = chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false))
    (hc2 : c 2 = chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true)) :
    (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k) ∧
    (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k) ∧
    ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {w | 0 ≤ c.coord 1 w ∧ 0 ≤ c.coord 2 w}) ∨
      ((∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k) ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k) ∧
      ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
        {w | c.coord 1 w ≤ 0 ∨ c.coord 2 w ≤ 0})) := by
  have hR (j : Bool) : T.region p (i, j) = R :=
    hregion (i, j) (((T.caps p).firstOuterTip_mem_carrier_iff i (i, j)).mpr rfl)
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip i) = z := by
    rw [← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have h1 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k := by
    refine ⟨(T.caps p).chordSupportingLine (i, true), ?_, ?_⟩
    · apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
      exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region (hR true)
    · apply affineBasis_first_coord_eq_smul_of_contact c _
        ((T.caps p).chordSupportingLine_spec (i, true)).1
      · rw [hc0, ← hp]
        exact (T.cap_contact_zero_at_outer_tips p (i, true) R (hR true)).1
      · rw [hc2]
        exact (T.cap_contact_zero_at_outer_tips p (i, true) R (hR true)).2
  have h2 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k := by
    refine ⟨(T.caps p).chordSupportingLine (i, false), ?_, ?_⟩
    · apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
      exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region (hR false)
    · apply affineBasis_second_coord_eq_smul_of_contact c _
        ((T.caps p).chordSupportingLine_spec (i, false)).1
      · rw [hc0, ← hp]
        exact (T.cap_contact_zero_at_outer_tips p (i, false) R (hR false)).1
      · rw [hc1]
        exact (T.cap_contact_zero_at_outer_tips p (i, false) R (hR false)).2
  have hf := T.core_frontier_first_outer_rays p R i hz hq hregion hband
  have hu : (⋃ j : Bool, (fun t : ℝ => z + t •
        (chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip j) - z)) '' Ici (0 : ℝ)) =
      (((fun t : ℝ => c 0 + t • (c 1 - c 0)) '' Ici (0 : ℝ)) ∪
        ((fun t : ℝ => c 0 + t • (c 2 - c 0)) '' Ici (0 : ℝ))) := by
    rw [hc0, hc1, hc2]
    ext w
    simp only [mem_iUnion, mem_union, Bool.exists_bool]
  rw [hu, ← hc0] at hf
  rcases mesh_support_germ_of_affine_rays (T.refined.mesh R) c hf with h | h
  · exact Or.inl ⟨h1, h2, h⟩
  · exact Or.inr ⟨h1, h2, h⟩

theorem second_outer_core_sector (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = z)
    (hc1 : c 1 = chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false))
    (hc2 : c 2 = chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true)) :
    (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k) ∧
    (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k) ∧
    ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {w | 0 ≤ c.coord 1 w ∧ 0 ≤ c.coord 2 w}) ∨
      ((∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k) ∧
      (∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k) ∧
      ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
        {w | c.coord 1 w ≤ 0 ∨ c.coord 2 w ≤ 0})) := by
  have hR (j : Bool) : T.region p (j, i) = R :=
    hregion (j, i) (((T.caps p).secondOuterTip_mem_carrier_iff i (j, i)).mpr rfl)
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip i) = z := by
    rw [← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have h1 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k := by
    refine ⟨(T.caps p).chordSupportingLine (true, i), ?_, ?_⟩
    · apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
      exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region (hR true)
    · apply affineBasis_first_coord_eq_smul_of_contact c _
        ((T.caps p).chordSupportingLine_spec (true, i)).1
      · rw [hc0, ← hp]
        exact (T.cap_contact_zero_at_outer_tips p (true, i) R (hR true)).2
      · rw [hc2]
        exact (T.cap_contact_zero_at_outer_tips p (true, i) R (hR true)).1
  have h2 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k := by
    refine ⟨(T.caps p).chordSupportingLine (false, i), ?_, ?_⟩
    · apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
      exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region (hR false)
    · apply affineBasis_second_coord_eq_smul_of_contact c _
        ((T.caps p).chordSupportingLine_spec (false, i)).1
      · rw [hc0, ← hp]
        exact (T.cap_contact_zero_at_outer_tips p (false, i) R (hR false)).2
      · rw [hc1]
        exact (T.cap_contact_zero_at_outer_tips p (false, i) R (hR false)).1
  have hf := T.core_frontier_second_outer_rays p R i hz hq hregion hband
  have hu : (⋃ j : Bool, (fun t : ℝ => z + t •
        (chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip j) - z)) '' Ici (0 : ℝ)) =
      (((fun t : ℝ => c 0 + t • (c 1 - c 0)) '' Ici (0 : ℝ)) ∪
        ((fun t : ℝ => c 0 + t • (c 2 - c 0)) '' Ici (0 : ℝ))) := by
    rw [hc0, hc1, hc2]
    ext w
    simp only [mem_iUnion, mem_union, Bool.exists_bool]
  rw [hu, ← hc0] at hf
  rcases mesh_support_germ_of_affine_rays (T.refined.mesh R) c hf with h | h
  · exact Or.inl ⟨h1, h2, h⟩
  · exact Or.inr ⟨h1, h2, h⟩

theorem first_outer_core_sector_fan (g : RiemannianMetric 2 S)
    (p : T.decomposition.vertices) (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = z)
    (hc1 : c 1 = chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false))
    (hc2 : c 2 = chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true)) :
    let μ := ∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) ((chartAt Plane (T.chart R : S)).symm (c 0))
    let α := g.cornerAngle ((chartAt Plane (T.chart R : S)).symm (c 0))
      ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 1 - c 0))
      ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 2 - c 0))
    ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {w | 0 ≤ c.coord 1 w ∧ 0 ≤ c.coord 2 w}) ∧ μ = α ∨
    ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {w | c.coord 1 w ≤ 0 ∨ c.coord 2 w ≤ 0}) ∧ μ = 2 * Real.pi - α := by
  have hz' : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support := hc0.symm ▸ hz
  rcases T.first_outer_core_sector p R i hz hq hregion hband c hc0 hc1 hc2 with
    ⟨h1, h2, hs⟩ | ⟨h1, h2, hs⟩
  · exact Or.inl ⟨hs, T.core_contribution_at_convex_sector g R c h1 h2 hz' hs⟩
  · exact Or.inr ⟨hs, T.core_contribution_at_reflex_sector g R c h1 h2 hz'
      (by rwa [compl_interior_convexSector])⟩

theorem second_outer_core_sector_fan (g : RiemannianMetric 2 S)
    (p : T.decomposition.vertices) (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = z)
    (hc1 : c 1 = chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false))
    (hc2 : c 2 = chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true)) :
    let μ := ∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) ((chartAt Plane (T.chart R : S)).symm (c 0))
    let α := g.cornerAngle ((chartAt Plane (T.chart R : S)).symm (c 0))
      ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 1 - c 0))
      ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 2 - c 0))
    ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {w | 0 ≤ c.coord 1 w ∧ 0 ≤ c.coord 2 w}) ∧ μ = α ∨
    ((T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {w | c.coord 1 w ≤ 0 ∨ c.coord 2 w ≤ 0}) ∧ μ = 2 * Real.pi - α := by
  have hz' : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support := hc0.symm ▸ hz
  rcases T.second_outer_core_sector p R i hz hq hregion hband c hc0 hc1 hc2 with
    ⟨h1, h2, hs⟩ | ⟨h1, h2, hs⟩
  · exact Or.inl ⟨hs, T.core_contribution_at_convex_sector g R c h1 h2 hz' hs⟩
  · exact Or.inr ⟨hs, T.core_contribution_at_reflex_sector g R c h1 h2 hz'
      (by rwa [compl_interior_convexSector])⟩

end RetainedCoordinateTriangulation
end PoincareConjecture.Topology.Surface
