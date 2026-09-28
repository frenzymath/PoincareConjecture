import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCoreGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.SectorComplements








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in


theorem core_contribution_eq_core_of_ne_zero (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (q : S)
    (hq : meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
      (T.refined.mesh R) q ≠ 0) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q) =
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refined.mesh R) q := by
  obtain ⟨u, v, hv, heq⟩ := mesh_exists_used_vertex_of_contribution_ne_zero
    g (T.refined.mesh R) (chartAt Plane (T.chart R : S)).symm q hq
  rw [← heq]
  exact T.core_contribution_at_used_vertex g R u v hv



theorem core_germ_of_collar_germ (R : T.decomposition.regions) {q : Plane}
    (hq : q ∈ (T.refined.mesh R).toPlaneComplex.support) (A : Set Plane)
    (hcollar : (chartAt Plane (T.chart R : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R
      =ᶠ[𝓝 q] A) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 q] (interior A)ᶜ := by
  have hc := T.core_complement_germ R q hq
  have hi := support_eventuallyEq_interior hcollar
  filter_upwards [hc, hi] with z hz hi
  change ((T.refined.mesh R).toPlaneComplex.support z) = ¬interior A z
  change ((T.refined.mesh R).toPlaneComplex.support z) = ¬interior _ z at hz
  rw [hi] at hz
  exact hz


theorem core_halfspace_germ_of_collar_germ (R : T.decomposition.regions) {q : Plane}
    (hq : q ∈ (T.refined.mesh R).toPlaneComplex.support)
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hcollar : (chartAt Plane (T.chart R : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R
      =ᶠ[𝓝 q] {z | l z ≤ 0}) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 q] {z | 0 ≤ l z} := by
  have h := T.core_germ_of_collar_germ R hq _ hcollar
  rw [interior_affine_halfspace_nonpos l hl] at h
  filter_upwards [h] with z hz
  apply propext
  change z ∈ (T.refined.mesh R).toPlaneComplex.support ↔ 0 ≤ l z
  have he : z ∈ (T.refined.mesh R).toPlaneComplex.support ↔ ¬l z < 0 := propext_iff.mp hz
  exact he.trans not_lt


theorem core_reflex_germ_of_collar_convex_germ (R : T.decomposition.regions)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hq : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hcollar : (chartAt Plane (T.chart R : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R
      =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ :=
  T.core_germ_of_collar_germ R hq _ hcollar


theorem core_convex_germ_of_collar_reflex_germ (R : T.decomposition.regions)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hq : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hcollar : (chartAt Plane (T.chart R : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R
      =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  have h := T.core_germ_of_collar_germ R hq _ hcollar
  rwa [compl_interior_reflexSector] at h

omit [T2Space S] in


theorem enclosing_refinement_monochromatic_of_scaled_contact
    (R : T.decomposition.regions) (b : AffineBasis (Fin 3) ℝ Plane)
    (first : List (Plane →ᵃ[ℝ] ℝ)) (l : Plane →ᵃ[ℝ] ℝ)
    (hlines : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ l = a • k) :
    ((TriangleMesh.single b b.ind).refineByLines
      (first ++ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R)).IsMonochromatic l := by
  obtain ⟨k, hk, a, _, rfl⟩ := hlines
  exact isMonochromatic_smul _ k
    ((TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem _
      (List.mem_append_right _ hk)) a

omit [T2Space S] in


theorem core_mesh_convex_sector_fan (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k)
    (h2 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k)
    (hq : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
      ((chartAt Plane (T.chart R : S)).symm (c 0)) =
      g.cornerAngle ((chartAt Plane (T.chart R : S)).symm (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 2 - c 0)) := by
  obtain ⟨b, first, P, heq, hinside⟩ := T.core_ancestry R
  have hsource : (T.coreMeshes R).toPlaneComplex.support ⊆ (chartAt Plane (T.chart R : S)).target := by
    rw [← T.refined.support R]
    exact T.refined.source R
  rw [T.refined.support R] at hq hlocal
  rw [heq] at hsource hq hlocal hinside
  rw [T.refined.mesh_eq_refineByLines R, heq]
  exact single_refineByLines_restrict_refineByLines_convexSector_fan_of_source g
    (chartAt Plane (T.chart R : S)).symm b c first _ P
    (T.enclosing_refinement_monochromatic_of_scaled_contact R b first _ h1)
    (T.enclosing_refinement_monochromatic_of_scaled_contact R b first _ h2)
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) hsource hq (hinside hq) hlocal

omit [T2Space S] in


theorem core_mesh_reflex_sector_fan (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k)
    (h2 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k)
    (hq : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ) :
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
      ((chartAt Plane (T.chart R : S)).symm (c 0)) =
      2 * Real.pi - g.cornerAngle ((chartAt Plane (T.chart R : S)).symm (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 2 - c 0)) := by
  obtain ⟨b, first, P, heq, hinside⟩ := T.core_ancestry R
  have hsource : (T.coreMeshes R).toPlaneComplex.support ⊆ (chartAt Plane (T.chart R : S)).target := by
    rw [← T.refined.support R]
    exact T.refined.source R
  rw [T.refined.support R] at hq hlocal
  rw [heq] at hsource hq hlocal hinside
  rw [T.refined.mesh_eq_refineByLines R, heq]
  exact single_refineByLines_restrict_refineByLines_reflexSector_fan_of_source g
    (chartAt Plane (T.chart R : S)).symm b c first _ P
    (T.enclosing_refinement_monochromatic_of_scaled_contact R b first _ h1)
    (T.enclosing_refinement_monochromatic_of_scaled_contact R b first _ h2)
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) hsource hq (hinside hq) hlocal

omit [T2Space S] in


theorem core_contribution_at_convex_sector (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k)
    (h2 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k)
    (hq : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) ((chartAt Plane (T.chart R : S)).symm (c 0))) =
      g.cornerAngle ((chartAt Plane (T.chart R : S)).symm (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 2 - c 0)) := by
  have h := T.core_mesh_convex_sector_fan g R c h1 h2 hq hlocal
  have ha := coordinateSectorAngle_mem_Ioo g (chartAt Plane (T.chart R : S)).symm c
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) (T.refined.source R hq)
  rw [T.core_contribution_eq_core_of_ne_zero g R _ (by rw [h]; exact ne_of_gt ha.1)]
  exact h

omit [T2Space S] in


theorem core_contribution_at_reflex_sector (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (c : AffineBasis (Fin 3) ℝ Plane)
    (h1 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 1 = a • k)
    (h2 : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ c.coord 2 = a • k)
    (hq : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) ((chartAt Plane (T.chart R : S)).symm (c 0))) =
      2 * Real.pi - g.cornerAngle ((chartAt Plane (T.chart R : S)).symm (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)) (c 2 - c 0)) := by
  have h := T.core_mesh_reflex_sector_fan g R c h1 h2 hq hlocal
  have ha := coordinateSectorAngle_mem_Ioo g (chartAt Plane (T.chart R : S)).symm c
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) (T.refined.source R hq)
  rw [T.core_contribution_eq_core_of_ne_zero g R _ (by rw [h]; linarith [Real.pi_pos, ha.2])]
  exact h

set_option maxHeartbeats 800000 in
omit [T2Space S] in


theorem core_contribution_at_new_canonical_vertex (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hzq : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hnew : ∀ t : (T.refined.mesh R).Triangle, z ∉ range (meshTriangleBasis (T.refined.mesh R) t)) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q.1) =
      if z ∈ interior (T.refined.mesh R).toPlaneComplex.support then 2 * Real.pi else Real.pi := by
  have heq (t : (T.refined.mesh R).Triangle) : T.refinement.mesh (.inr (.inr ⟨R, t⟩)) =
      (TriangleMesh.single (meshTriangleBasis (T.refined.mesh R) t)
        (meshTriangleBasis (T.refined.mesh R) t).ind).refineByLines
          (T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inr ⟨R, t⟩))).mesh_eq_refineByLines
  simp_rw [heq]
  rw [← hzq]
  apply independently_refined_mesh_new_vertex_fan g (chartAt Plane (T.chart R : S)).symm
    (T.refined.mesh R) (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) (T.refined.source R) _ hz hnew
  intro t ht
  have hw := T.core_parent_used_vertex R q hzq t ht
  rw [heq t] at hw
  exact hw

omit [T2Space S] in


theorem core_contribution_at_straight_canonical_vertex (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hzq : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hlines : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ l = a • k)
    (hlz : l z = 0)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z] {w | 0 ≤ l w}) :
    (∑ t : (T.refined.mesh R).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q.1) = Real.pi := by
  by_cases hold : ∃ t : (T.refined.mesh R).Triangle, z ∈ range (meshTriangleBasis (T.refined.mesh R) t)
  · obtain ⟨t, ht⟩ := hold
    rw [range_meshTriangleBasis] at ht
    obtain ⟨v, hv, hpos⟩ := ht
    have h := T.core_mesh_straight_boundary_fan_of_scaled_contact g R l hl hlines t v hv
      (hpos.symm ▸ hlz) (hpos.symm ▸ hlocal)
    rw [hpos, hzq] at h
    rw [T.core_contribution_eq_core_of_ne_zero g R _ (by rw [h]; exact Real.pi_ne_zero)]
    exact h
  · rw [T.core_contribution_at_new_canonical_vertex g R q hzq hz (fun t ht => hold ⟨t, ht⟩)]
    rw [if_neg]
    intro hzi
    have hli := hlocal.mem_interior_iff.mp hzi
    rw [interior_affine_halfspace_nonneg l hl] at hli
    exact (ne_of_gt hli) hlz

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
