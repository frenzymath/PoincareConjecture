import PoincareConjecture.Proofs.M35.Thm12_28.SliceCylinders
import Mathlib.Topology.LocallyConstant.Basic










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem cylinder_spatial_locallyConstant {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    {x : C.carrier} (hx : x ∈ U) :
    IsLocallyConstant (fun s : I => (e.forward s.val s.property x).val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro s
  obtain ⟨b, y, δ, hδ, hcompat⟩ := e.vertical_compatibility s.val s.property x hx
  have hy : (e.forward s.val s.property x).val = y := by
    obtain ⟨_, heq⟩ := hcompat s.val s.property (by simpa only [sub_self, abs_zero] using hδ)
    exact congrArg Subtype.val heq
  filter_upwards [(continuous_subtype_val.tendsto s).eventually (Metric.ball_mem_nhds s.val hδ)]
    with s' hs'
  obtain ⟨_, heq⟩ := hcompat s'.val s'.property
    (by simpa only [Metric.mem_ball, Real.dist_eq] using hs')
  exact (congrArg Subtype.val heq).trans hy.symm



theorem cylinder_spatial_eq {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hI : IsPreconnected I) {x : C.carrier} (hx : x ∈ U)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    (e.forward s hs x).val = (e.forward t ht x).val := by
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
  exact (cylinder_spatial_locallyConstant F e hx).apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩



theorem cylinder_curvature_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {a Q : ℝ}
    {I : Set ℝ} {U : Set (slice J a).carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) (slice J a) a Q I U)
    (hI : IsPreconnected I) (h₀ : 0 ∈ I)
    (hzero : ∀ x ∈ U, e.pointMap 0 h₀ x = (⟨a, x⟩ : (generalizedFlow F).point))
    {s : ℝ} (hs : s ∈ I) {x : (slice J a).carrier} (hx : x ∈ U) :
    (generalizedFlow F).curvatureNorm (e.pointMap s hs x) =
      (F.connection (a + s / Q)).curvatureTensorNorm x.val := by
  have hzero' : (e.forward 0 h₀ x).val = x.val :=
    congrArg (fun p : (generalizedFlow F).point => p.2.val) (hzero x hx)
  have hsp := (cylinder_spatial_eq F e hI hx hs h₀).trans hzero'
  exact (curvatureNorm_eq P F (e.forward s hs x).property (e.forward s hs x).val).trans
    (congrArg (F.connection (a + s / Q)).curvatureTensorNorm hsp)

end PoincareConjecture.M35.OrdinaryRealization
