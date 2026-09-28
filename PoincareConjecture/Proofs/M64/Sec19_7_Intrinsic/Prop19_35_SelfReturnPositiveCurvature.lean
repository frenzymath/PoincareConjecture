import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicReturnTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicRegionPositiveCurvature













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture





theorem m64Intrinsic_geodesic_selfintersection_positive_curvature
    {G : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData G)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (h0 : ‖gamma 0‖ = 1)
    (hinside : ∀ x ∈ Ioc 0 T, 1 < ‖gamma x‖ ∧ ‖gamma x‖ ≤ 2)
    (hunit : ∀ x ∈ Icc 0 T, G.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1)
    (hnot : ¬ InjOn gamma (Icc 0 T)) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
      closure U ∪ closure V = univ ∧ IsCompact (closure U) ∧
      (closure U ⊆ standardAnnulusDomain ∨ Metric.closedBall (0 : AnnulusCoordinates) 1 ⊆ U) ∧
      Real.pi ≤ ∫ x in closure U, D.scalarCurvature x / 2 ∂G.volumeMeasure := by
  obtain ⟨s, t, g, _, hst, _, hchoice, hgg, hgggeo, hge, hgi, hgu, _, U, V,
    hU, hV, hpU, hpV, hdisj, hpartition, hfU, hfV, hcompact, hdichotomy,
    m, face, C, b, hC, hCi, hsource, hcarrier, hboundary, hfront, hinter, hcover⟩ :=
    m64Intrinsic_geodesic_selfintersection_triangulation G hg hgeo h0 hinside hunit hnot
  have himage : g '' Icc 0 (t - s) = gamma '' Icc s t := by
    rcases hchoice with heq | heq
    · rw [heq]
      change (gamma ∘ fun x => s + x) '' Icc 0 (t - s) = _
      rw [image_comp, image_const_add_Icc]
      congr 1
      congr 1 <;> ring
    · rw [heq]
      change (gamma ∘ fun x => t - x) '' Icc 0 (t - s) = _
      rw [image_comp, image_const_sub_Icc]
      congr 1
      congr 1 <;> ring
  have hclosure : closure U ∪ closure V = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ gamma '' Icc s t
    · left
      apply frontier_subset_closure
      rwa [hfU, himage]
    · have hz' : z ∈ U ∪ V := hpartition.symm ▸ hz
      exact hz'.elim (fun h => Or.inl (subset_closure h)) (fun h => Or.inr (subset_closure h))
  refine ⟨U, V, hU, hV, hpU, hpV, hdisj, hclosure, hcompact, hdichotomy, ?_⟩
  exact m64Intrinsic_geodesic_return_region_curvature_ge_pi face C b hC hCi hsource
    hcarrier hboundary hinter hfront D hgg (sub_pos.mpr hst) hge hgi hgggeo hgu
      hU hV hdisj hfU hfV hclosure hpV.isConnected.isPreconnected hcover

end PoincareConjecture
