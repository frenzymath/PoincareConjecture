import PoincareConjecture.Statements.M47CanonicalInduction
import PoincareConjecture.Proofs.M12.GeneralizedCylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open PoincareConjecture.Proofs.M12

theorem exists_component_regular_cylinder_ordinary
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {W : M33RegularHistoryWindow F} (H : M33RegularHistoryData W)
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
    {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
    (e : SurgeryFlowCylinder F C origin scale J.domain U)
    (htime : ∀ s ∈ J.domain, origin + s / scale ∈ W.interval)
    (hregular : ∀ s hs, e.forward s hs '' (U : Set C.carrier) ⊆
      m33RegularRegion F (origin + s / scale)) :
    ∃ G : RicciFlow 3 U ((fun s : ℝ => origin + s / scale) '' J.domain),
      ∀ (s : ℝ) (hs : s ∈ J.domain) (x : U) (v w : TangentSpace (𝓡 3) x),
        (F.metric (origin + s / scale)).inner (e.forward s hs x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) =
            (G.metric (origin + s / scale)).inner x v w := by
  have htG : ∀ s ∈ J.domain, origin + s / scale ∈ H.generalized.interval := by
    intro s hs
    rw [H.interval_eq]
    exact htime s hs
  obtain ⟨d, _hpoints, hpullback⟩ :=
    H.cylinders_from_surgery C origin scale J.domain U U.isOpen htG e hregular
  obtain ⟨geometry⟩ := flowBoxRicciGeometry H.generalized P.m11 P.m12
  let R := geometry.realization
  have hphysical : (cylinderPhysicalInterval origin scale d.scale_pos J).domain ⊆
      H.generalized.interval := by
    rintro _ ⟨s, hs, rfl⟩
    exact htG s hs
  let metric := rawCylinderMetric R d hphysical
  let gauges := P.m12.gauges H.generalized.point Sigma.fst (flowInterval H.generalized)
    R.spacetime R.slices R.timeIntervals R.gaugeCover geometry.leafwise
  obtain ⟨ordinary⟩ := gauges.compatible_ordinary U
    (cylinderPhysicalInterval origin scale d.scale_pos J)
    (rawCylinderTransport R d hphysical) metric (fun p _hp => geometry.equation p)
  refine ⟨ordinary.flow, ?_⟩
  intro s hs x v w
  have hm := rawCylinderMetric_eq R d hphysical metric ⟨s, hs⟩
    (geometry.sliceIdentification (origin + s / scale)) x v w
  rw [hpullback s hs x.val x.property] at hm
  have hforward : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (e.forward s hs) x.val :=
    (e.forward_smooth s hs x.val x.property).contMDiffAt (U.isOpen.mem_nhds x.property)
  have hder := mfderiv_comp x (hforward.mdifferentiableAt (by simp))
    (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x = _ at hder
  rw [ordinary.metric_eq, hder]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hm]
  dsimp only [SurgeryFlowCylinder.pullbackInner]
  exact (mul_div_cancel_left₀ _ e.scale_pos.ne').symm

end PoincareConjecture.M47
