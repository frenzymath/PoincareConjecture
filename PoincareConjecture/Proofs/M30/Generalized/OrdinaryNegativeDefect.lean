import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Definitions.M11AdaptedAtlas
import PoincareConjecture.Proofs.M13.ConnectionScale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30.Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}

theorem negativeCurvaturePart_of_ordinaryFlow
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (G : RicciFlow 3 U J.domain)
    (hG : ∀ s (hs : s ∈ J.domain) (x : U) (v w : TangentSpace (𝓡 3) x),
      (G.metric s).inner x v w =
        e.pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (s : ℝ) (hs : s ∈ J.domain) (x : U) :
    (G.connection s).negativeCurvaturePart x =
      (F.connection (e.pointMap s hs x.val).1).negativeCurvaturePart
        (e.pointMap s hs x.val).2 / scale := by
  let f : U → (F.slice (origin + s / scale)).carrier := fun y => e.forward s hs y.val
  let h := M13.scaleSmoothMetric (F.metric (origin + s / scale)) scale e.scale_pos
  let D := M13.scaleLeviCivitaData (F.connection (origin + s / scale)) scale e.scale_pos
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := by
    intro y
    exact ((e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val y)
  have hmetric : ∀ y ∈ (univ : Set U), ∀ v w : TangentSpace (𝓡 3) y,
      (G.metric s).inner y v w = h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    intro y _ v w
    have hforward := (e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)
    have hder := mfderiv_comp y (hforward.mdifferentiableAt (by simp))
      (contMDiff_subtype_val (n := ∞) y |>.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) f y = _ at hder
    rw [hG s hs y v w]
    change _ = scale * (F.metric (origin + s / scale)).inner (f y)
      (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w)
    rw [hder]
    rfl
  have hlocal := MetricSurgery.negativeCurvaturePart_eq_of_local_isometry
    (G.connection s) D isOpen_univ hf.contMDiffOn hmetric (mem_univ x)
  have hscale := MetricSurgery.negativeCurvaturePart_positiveScaling_const
    (F.connection (origin + s / scale)) e.scale_pos D (f x)
  change (G.connection s).negativeCurvaturePart x =
    (F.connection (origin + s / scale)).negativeCurvaturePart (f x) / scale
  simpa only [div_eq_mul_inv, mul_comm] using hlocal.trans hscale

end PoincareConjecture.M30.Cylinder
