import PoincareLib.Geometry.RicciFlow.Blowup.Construction.SourceNames
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareLib.Geometry.Spacetime.Atlas
import PoincareLib.Geometry.Riemannian.Homothety.Connection.Scaling
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching

/-!
# Negative-curvature normalization on an ordinary cylinder

Morgan--Tian Definition 3.40, p. 61, and Corollary 11.3, p. 269,
with the curvature conventions of pp. 5-7. The actual ordinary metric
is the normalized pullback of the generalized metric. Local-isometry
invariance and positive scaling identify the native negative part for
the retained connections at every included time, including endpoints.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M30.Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}

/-- The actual ordinary connection has the negative-curvature normalization
of Definition 3.40, p. 61, used in Corollary 11.3, p. 269. This is a
spatial identity on the open source at every included time. -/
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

end PoincareMT.M30.Cylinder
