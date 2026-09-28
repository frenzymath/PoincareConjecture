import PoincareConjecture.Proofs.M30.Generalized.OrdinaryExtraction
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M13.ContractionTransport











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30.Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}




theorem curvature_of_ordinaryFlow
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (G : RicciFlow 3 U J.domain)
    (hG : ∀ s (hs : s ∈ J.domain) (x : U) (v w : TangentSpace (𝓡 3) x),
      (G.metric s).inner x v w =
        e.pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (s : ℝ) (hs : s ∈ J.domain) (x : U) :
    (G.connection s).scalarCurvature x = F.scalar (e.pointMap s hs x.val) / scale ∧
      (G.connection s).curvatureTensorNorm x =
        F.curvatureNorm (e.pointMap s hs x.val) / scale := by
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
  have hscalar := (G.connection s).scalarCurvature_eq_of_local_isometry D
    isOpen_univ hf.contMDiffOn hmetric (mem_univ x)
  have hnorm := (G.connection s).curvatureTensorNorm_eq_of_local_isometry D
    isOpen_univ hf.contMDiffOn hmetric (mem_univ x)
  have hhom := M13.identity_metricHomothety
    (F.metric (origin + s / scale)) scale e.scale_pos
  have hscalarScale := M13.homothety_scalarCurvature_eq
    (F.metric (origin + s / scale)) h
    (Diffeomorph.refl (𝓡 3) (F.slice (origin + s / scale)).carrier ∞)
    scale e.scale_pos hhom (F.connection (origin + s / scale)) D (f x)
  have hnormScale := M13.homothety_curvatureTensorNorm_eq
    (F.metric (origin + s / scale)) h
    (Diffeomorph.refl (𝓡 3) (F.slice (origin + s / scale)).carrier ∞)
    scale e.scale_pos hhom (F.connection (origin + s / scale)) D (f x)
  exact ⟨hscalar.trans hscalarScale, hnorm.trans hnormScale⟩

end PoincareConjecture.M30.Cylinder
