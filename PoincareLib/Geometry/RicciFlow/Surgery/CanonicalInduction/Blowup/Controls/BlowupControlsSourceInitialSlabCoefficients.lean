import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialNeckChart
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialCenteredMetric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialRawPast
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckMetric

/-!
# Literal old coefficients on the actual ordinary source

Whole-source agreement at a shared raw time gives an equality of metric
germs. The fixed subtype chart then reads precisely the original old
cylinder tensor, including its scale and both native tangent slots.
Morgan--Tian Lemma 17.7, pp. 405-406; I8E1-E4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- At every actual cylinder time the displayed tensor is the genuine
composition of two continuous linear differentials with the metric. -/
theorem source_initial_cylinder_tensor_bilinear
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (coordinate : RoundCylinderSpace → C.carrier) (s : ℝ) (hs : s ∈ I)
    (z : RoundCylinderSpace) :
    ∃ L : V →L[ℝ] V →L[ℝ] ℝ,
      ∀ v w, L v w = surgeryCylinderPullback e coordinate s z v w := by
  let A : V →L[ℝ] E := (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (coordinate z)).comp
    (mfderiv IC (𝓡 3) coordinate z)
  let H : E →L[ℝ] E →L[ℝ] ℝ := (F.metric (origin + s / scale)).inner
    (e.forward s hs (coordinate z))
  refine ⟨scale • H.bilinearComp A A, ?_⟩
  intro v w
  simp only [surgeryCylinderPullback, dif_pos hs]
  rfl

private theorem initialCylinder_metric_agreement
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I J : Set ℝ} {U W : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : SurgeryFlowCylinder F C origin scale J W) (hU : IsOpen U)
    {s : ℝ} (hs : s ∈ I) (ht : s ∈ J)
    (hmap : EqOn (e.forward s hs) (f.forward s ht) U)
    {x : C.carrier} (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner s hs x v w = f.pullbackInner s ht x v w := by
  have heq : e.forward s hs =ᶠ[𝓝 x] f.forward s ht := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hmap hy
  simp only [SurgeryFlowCylinder.pullbackInner, heq.mfderiv_eq]
  exact congrArg (fun y : (F.slice (origin + s / scale)).carrier =>
    scale * (F.metric (origin + s / scale)).inner y
      (mfderiv (𝓡 3) (𝓡 3) (f.forward s ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (f.forward s ht) x w)) (hmap hx)

/-- The ordinary source metric has exactly the old centered coefficient
field throughout the literal chart ball at every shared raw time. -/
theorem source_initial_slab_coefficients
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {origin scale : ℝ} {I J : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier)
    (D : SurgeryFlowCylinder F C origin scale I U)
    (old : SurgeryFlowCylinder F C origin scale J N.carrier)
    (s : ℝ) (hs : s ∈ I) (hold : s ∈ J)
    (hagreement : ∀ x ∈ U, D.forward s hs x = old.forward s hold x)
    (gU : RiemannianMetric 3 U)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      gU.inner x v w = D.pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (theta : UnitTwoSphere) (c : ℝ)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Phi.source = Metric.ball 0 (1 / 2))
    (hmap : ∀ p ∈ Metric.ball (0 : E) (1 / 2),
      (Phi p).val = centeredNeckLift N theta c p)
    (hdomain : Metric.ball (0 : E) (1 / 2) ⊆ centeredNeckDomain N c)
    {p : E} (hp : p ∈ Metric.ball 0 (1 / 2)) :
    gU.pullbackCoefficients Phi p =
      centeredCylinderMetric (surgeryCylinderPullback old N.coordinate_map s) theta c p := by
  obtain ⟨L, hL⟩ := source_initial_cylinder_tensor_bilinear old N.coordinate_map s hold
    (centeredCylinderLift theta c p)
  have hd := source_initial_neck_chart_differential N U theta c Phi hsource hmap hp
  have hpoint : centeredNeckLift N theta c p ∈ U :=
    (hmap p hp) ▸ (Phi p).property
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change gU.inner (Phi p) (mfderiv (𝓡 3) (𝓡 3) Phi p v)
    (mfderiv (𝓡 3) (𝓡 3) Phi p w) = _
  rw [hmetric]
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Phi p)
    (mfderiv (𝓡 3) (𝓡 3) Phi p v) =
      mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta c) p v at hv
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Phi p)
    (mfderiv (𝓡 3) (𝓡 3) Phi p w) =
      mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta c) p w at hw
  rw [hv, hw, hmap p hp,
    initialCylinder_metric_agreement D old U.isOpen hs hold hagreement hpoint]
  rw [source_initial_centered_tensor_evaluation _ theta c p L hL v w]
  simp only [surgeryCylinderPullback, dif_pos hold]
  rw [centeredCylinderLift_mfderiv, centeredCylinderLift_mfderiv,
    ← centeredNeckLift_mfderiv N theta c (hdomain hp),
    ← centeredNeckLift_mfderiv N theta c (hdomain hp)]
  rfl

end PoincareMT.M47
