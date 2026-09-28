import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderRicciFlow









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  {e : SurgeryFlowCylinder F C origin scale I U}
  {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}




theorem CylinderRicciFlow.pullback_eq_cylinder
    (G : CylinderRicciFlow e f) (hmap : f.target ⊆ U)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (s : ℝ) (hs : s ∈ I) {x : E} (hx : x ∈ f.source) (v w : E) :
    (G.flow.metric s).pullbackCoefficients (targetChart f p) x v w =
      e.pullbackInner s hs (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  let g := m01RescaledMetric (F.metric (origin + s / scale)) scale e.scale_pos
  have heq : e.forward s hs ∘ f =ᶠ[nhds x]
      cylinderTargetTransport e f s hs ∘ targetChart f p := by
    filter_upwards [f.open_source.mem_nhds hx] with y hy
    change e.forward s hs (f y) = e.forward s hs (targetChart f p y).1
    rw [targetChart_val f p hy]
  have hcoeff := pullbackCoefficients_eq_of_metric_germ (G.flow.metric s) g
    ((cylinderTargetTransport_smooth e f hmap s hs).mdifferentiable (by simp) _)
    (((contMDiffOn_targetChart f p).contMDiffAt
      (f.open_source.mem_nhds hx)).mdifferentiableAt (by simp)) heq
    (fun a b => (G.metric_link s hs (targetChart f p x) a b).symm)
  have hnorm : (G.flow.metric s).pullbackCoefficients (targetChart f p) x v w =
      scale * cylinderPhysicalCoefficients e f s hs x v w := by
    exact congrArg (fun B : V => B v w) hcoeff.symm
  rw [hnorm]
  have hdf := (f.contMDiffOn.contMDiffAt (f.open_source.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hde := (((e.forward_smooth s hs).mono hmap).contMDiffAt
    (f.open_target.mem_nhds (f.map_source hx))).mdifferentiableAt (by simp)
  change scale * (F.metric (origin + s / scale)).inner ((e.forward s hs ∘ f) x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x w) = _
  rw [mfderiv_comp x hde hdf]
  rfl




theorem CylinderRicciFlow.metricJetError_eq_cylinder
    (G : CylinderRicciFlow e f) (hmap : f.target ⊆ U)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (s : ℝ) (hs : s ∈ I) {x : E} (hx : x ∈ f.source)
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (m : ℕ) :
    singularMetricJetErrorSquared g D
      (fun y v => (G.flow.metric s).pullbackCoefficients (targetChart f p) y (v 0) (v 1))
      m x =
    singularMetricJetErrorSquared g D
      (fun y v => e.pullbackInner s hs (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y (v 0)) (mfderiv (𝓡 3) (𝓡 3) f y (v 1))) m x := by
  apply singularMetricJetErrorSquared_congr_germ
  filter_upwards [f.open_source.mem_nhds hx] with y hy
  funext v
  exact G.pullback_eq_cylinder hmap p s hs hy (v 0) (v 1)

end PoincareConjecture.M44
