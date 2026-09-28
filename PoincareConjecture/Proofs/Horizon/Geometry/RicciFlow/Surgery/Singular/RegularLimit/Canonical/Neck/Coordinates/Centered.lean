import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ReferenceCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckMetric



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
  {t ε : ℝ} (ht : t ∈ Ico H.reference.tMinus T)

theorem regularNeckSourceMap_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.regularNeckSourceMap P04 ht) :=
  (H.reference.forward_smooth t ht).comp contMDiff_subtype_val

theorem regularNeckSourceMap_metric
    (x : H.regularRegion P04) (v w : TangentSpace (𝓡 3) x) :
    (F.metric t).inner (H.regularNeckSourceMap P04 ht x)
        (mfderiv (𝓡 3) (𝓡 3) (H.regularNeckSourceMap P04 ht) x v)
        (mfderiv (𝓡 3) (𝓡 3) (H.regularNeckSourceMap P04 ht) x w) =
      ((H.terminalFlow P04).metric t).inner x v w := by
  change (F.metric t).inner (H.regularNeckSourceMap P04 ht x)
      (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht ∘ Subtype.val) x v)
      (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht ∘ Subtype.val) x w) = _
  rw [mfderiv_comp x ((H.reference.forward_smooth t ht x).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x),
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  change (F.metric t).inner (H.reference.forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht) x w) = _
  rw [H.reference.metric_pullback]
  exact (H.terminalMetricFamily_inner_of_ne P04 ht.2.ne x v w).symm

variable (N : GeneralizedStrongNeck F t ε) (hε : ε < 1 / 2)
  (x₀ : H.regularRegion P04)

def regularNeckCenteredLift (z : RoundCylinderSpace) : E → H.regularRegion P04 :=
  SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘
    (H.reference.inverse t ht ∘ centeredNeckLift (N.spatialNeck hε) z.1 z.2)

variable (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet)

include hcapture

theorem regularNeckCenteredLift_val (z : RoundCylinderSpace) {p : E}
    (hp : p ∈ centeredNeckDomain (N.spatialNeck hε) z.2) :
    (H.regularNeckCenteredLift P04 ht N hε x₀ z p : M) =
      H.reference.inverse t ht (centeredNeckLift (N.spatialNeck hε) z.1 z.2 p) :=
  SingularRegularLimit.openRetraction_val _ _
    (hcapture (centeredNeckLift_mem (N.spatialNeck hε) z.1 z.2 hp))

theorem regularNeckCenteredLift_source (z : RoundCylinderSpace) {p : E}
    (hp : p ∈ centeredNeckDomain (N.spatialNeck hε) z.2) :
    H.regularNeckSourceMap P04 ht (H.regularNeckCenteredLift P04 ht N hε x₀ z p) =
      centeredNeckLift (N.spatialNeck hε) z.1 z.2 p := by
  change H.reference.forward t ht (H.regularNeckCenteredLift P04 ht N hε x₀ z p : M) = _
  rw [H.regularNeckCenteredLift_val P04 ht N hε x₀ hcapture z hp,
    H.reference.right_inverse]

theorem regularNeckCenteredLift_smooth (z : RoundCylinderSpace) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (H.regularNeckCenteredLift P04 ht N hε x₀ z)
      (centeredNeckDomain (N.spatialNeck hε) z.2) := by
  apply SingularRegularLimit.contMDiffOn_openRetraction_comp
  · apply (H.reference.inverse_smooth t ht).comp_contMDiffOn
    intro p hp
    exact (centeredNeckLift_contMDiffAt (N.spatialNeck hε) z.1 z.2 hp).contMDiffWithinAt
  · intro p hp
    exact hcapture (centeredNeckLift_mem (N.spatialNeck hε) z.1 z.2 hp)

theorem regularNeckCenteredLift_mfderiv_invertible (z : RoundCylinderSpace) {p : E}
    (hp : p ∈ centeredNeckDomain (N.spatialNeck hε) z.2) :
    (mfderiv (𝓡 3) (𝓡 3) (H.regularNeckCenteredLift P04 ht N hε x₀ z) p).IsInvertible := by
  let f := H.regularNeckCenteredLift P04 ht N hε x₀ z
  let k := centeredNeckInverse (N.spatialNeck hε) z.1 z.2 ∘ H.regularNeckSourceMap P04 ht
  have hU := centeredNeckDomain_isOpen (N.spatialNeck hε) z.2
  have hf := ((H.regularNeckCenteredLift_smooth P04 ht N hε x₀ hcapture z).contMDiffAt
    (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have hkinv := centeredNeckInverse_contMDiffAt_lift (N.spatialNeck hε) z.1 z.2 hp
  rw [← H.regularNeckCenteredLift_source P04 ht N hε x₀ hcapture z hp] at hkinv
  have hk : MDifferentiableAt (𝓡 3) (𝓡 3) k (f p) :=
    (hkinv.comp _ (H.regularNeckSourceMap_smooth P04 ht _)).mdifferentiableAt (by simp)
  have hlocal : k ∘ f =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with y hy
    change centeredNeckInverse (N.spatialNeck hε) z.1 z.2
      (H.regularNeckSourceMap P04 ht (H.regularNeckCenteredLift P04 ht N hε x₀ z y)) = y
    rw [H.regularNeckCenteredLift_source P04 ht N hε x₀ hcapture z hy]
    exact centeredNeckInverse_lift (N.spatialNeck hε) z.1 z.2 hy
  have hi := mfderiv_injective_of_local_leftInverse hf hk hlocal
  let L : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) f p
  have hs : Function.Surjective L := LinearMap.surjective_of_injective (f := L.toLinearMap) hi
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩



theorem regularNeckCenteredLift_coefficients (z : RoundCylinderSpace) {p : E}
    (hp : p ∈ centeredNeckDomain (N.spatialNeck hε) z.2) :
    ((H.terminalFlow P04).metric t).pullbackCoefficients
        (H.regularNeckCenteredLift P04 ht N hε x₀ z) p =
      (F.metric t).pullbackCoefficients (centeredNeckLift (N.spatialNeck hε) z.1 z.2) p := by
  let f := H.regularNeckCenteredLift P04 ht N hε x₀ z
  let g := H.regularNeckSourceMap P04 ht
  let e := centeredNeckLift (N.spatialNeck hε) z.1 z.2
  have heq : g ∘ f =ᶠ[𝓝 p] e := by
    filter_upwards [(centeredNeckDomain_isOpen (N.spatialNeck hε) z.2).mem_nhds hp] with y hy
    exact H.regularNeckCenteredLift_source P04 ht N hε x₀ hcapture z hy
  have hf := ((H.regularNeckCenteredLift_smooth P04 ht N hε x₀ hcapture z).contMDiffAt
    ((centeredNeckDomain_isOpen (N.spatialNeck hε) z.2).mem_nhds hp)).mdifferentiableAt (by simp)
  have hg := (H.regularNeckSourceMap_smooth P04 ht (f p)).mdifferentiableAt (by simp)
  have hd := (mfderiv_comp p hg hf).symm.trans heq.mfderiv_eq
  ext v w
  change ((H.terminalFlow P04).metric t).inner (f p)
      (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w) = _
  rw [← H.regularNeckSourceMap_metric P04 ht]
  have hv : mfderiv (𝓡 3) (𝓡 3) g (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) =
      mfderiv (𝓡 3) (𝓡 3) e p v := congrArg (fun A : E →L[ℝ] E => A v) hd
  have hw : mfderiv (𝓡 3) (𝓡 3) g (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) =
      mfderiv (𝓡 3) (𝓡 3) e p w := congrArg (fun A : E →L[ℝ] E => A w) hd
  erw [hv, hw]
  exact congrArg (fun y : (F.slice t).carrier => (F.metric t).inner y
    (mfderiv (𝓡 3) (𝓡 3) e p v) (mfderiv (𝓡 3) (𝓡 3) e p w)) heq.self_of_nhds

theorem regularNeckCenteredLift_metric_jet (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (j : ℕ) :
    iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
      (H.regularNeckCenteredLift P04 ht N hε x₀ z)) 0 =
      iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients
        (centeredNeckLift (N.spatialNeck hε) z.1 z.2)) 0 := by
  apply Filter.EventuallyEq.eq_of_nhds
  apply Filter.EventuallyEq.iteratedFDeriv
  filter_upwards [(centeredNeckDomain_isOpen (N.spatialNeck hε) z.2).mem_nhds
    (zero_mem_centeredNeckDomain (N.spatialNeck hε) hz)] with p hp
  exact H.regularNeckCenteredLift_coefficients P04 ht N hε x₀ hcapture z hp

end PoincareConjecture.SingularTimeAssumptions
