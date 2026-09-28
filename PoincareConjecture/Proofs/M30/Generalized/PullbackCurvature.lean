import PoincareConjecture.Proofs.M30.Generalized.OrdinaryCurvature
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryNegativeDefect

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M30.Cylinder

theorem curvature_of_pullbackFlow
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    {Y : Type v} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
    (f : Y → C.carrier) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (himage : ∀ x, f x ∈ U) (G : RicciFlow 3 Y J.domain)
    (hG : ∀ s (hs : s ∈ J.domain) (x : Y) (v w : TangentSpace (𝓡 3) x),
      (G.metric s).inner x v w = e.pullbackInner s hs (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (s : ℝ) (hs : s ∈ J.domain) (x : Y) :
    (G.connection s).scalarCurvature x = F.scalar (e.pointMap s hs (f x)) / scale ∧
      (G.connection s).curvatureTensorNorm x =
        F.curvatureNorm (e.pointMap s hs (f x)) / scale ∧
      (G.connection s).negativeCurvaturePart x =
        (F.connection (e.pointMap s hs (f x)).1).negativeCurvaturePart
          (e.pointMap s hs (f x)).2 / scale := by
  let q : Y → (F.slice (origin + s / scale)).carrier := e.forward s hs ∘ f
  let h := M13.scaleSmoothMetric (F.metric (origin + s / scale)) scale e.scale_pos
  let D := M13.scaleLeviCivitaData (F.connection (origin + s / scale)) scale e.scale_pos
  have hq : ContMDiff (𝓡 3) (𝓡 3) ∞ q := by
    intro y
    exact ((e.forward_smooth s hs (f y) (himage y)).contMDiffAt
      (U.isOpen.mem_nhds (himage y))).comp y (hf y)
  have hmetric : ∀ y ∈ (univ : Set Y), ∀ v w : TangentSpace (𝓡 3) y,
      (G.metric s).inner y v w = h.inner (q y)
        (mfderiv (𝓡 3) (𝓡 3) q y v) (mfderiv (𝓡 3) (𝓡 3) q y w) := by
    intro y _ v w
    have hforward := (e.forward_smooth s hs (f y) (himage y)).contMDiffAt
      (U.isOpen.mem_nhds (himage y))
    have hderiv := mfderiv_comp y (hforward.mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) q y = _ at hderiv
    rw [hG s hs y v w]
    change _ = scale * (F.metric (origin + s / scale)).inner (q y)
      (mfderiv (𝓡 3) (𝓡 3) q y v) (mfderiv (𝓡 3) (𝓡 3) q y w)
    rw [hderiv]
    rfl
  have hscalar := (G.connection s).scalarCurvature_eq_of_local_isometry D
    isOpen_univ hq.contMDiffOn hmetric (mem_univ x)
  have hnorm := (G.connection s).curvatureTensorNorm_eq_of_local_isometry D
    isOpen_univ hq.contMDiffOn hmetric (mem_univ x)
  have hnegative := MetricSurgery.negativeCurvaturePart_eq_of_local_isometry
    (G.connection s) D isOpen_univ hq.contMDiffOn hmetric (mem_univ x)
  have hhom := M13.identity_metricHomothety
    (F.metric (origin + s / scale)) scale e.scale_pos
  have hscalarScale := M13.homothety_scalarCurvature_eq
    (F.metric (origin + s / scale)) h
    (Diffeomorph.refl (𝓡 3) (F.slice (origin + s / scale)).carrier ∞)
    scale e.scale_pos hhom (F.connection (origin + s / scale)) D (q x)
  have hnormScale := M13.homothety_curvatureTensorNorm_eq
    (F.metric (origin + s / scale)) h
    (Diffeomorph.refl (𝓡 3) (F.slice (origin + s / scale)).carrier ∞)
    scale e.scale_pos hhom (F.connection (origin + s / scale)) D (q x)
  have hnegativeScale := MetricSurgery.negativeCurvaturePart_positiveScaling_const
    (F.connection (origin + s / scale)) e.scale_pos D (q x)
  refine ⟨hscalar.trans hscalarScale, hnorm.trans hnormScale, ?_⟩
  change (G.connection s).negativeCurvaturePart x =
    (F.connection (origin + s / scale)).negativeCurvaturePart (q x) / scale
  simpa only [div_eq_mul_inv, mul_comm] using hnegative.trans hnegativeScale

end PoincareConjecture.M30.Cylinder
