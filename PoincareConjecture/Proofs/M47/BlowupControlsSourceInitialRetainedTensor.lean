import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOlderTensor
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialClosedCylinder
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem source_initial_retained_limit_metric
    {F : SurgeryFlowData.{u}} {T : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    {x : (F.event T hT).terminal.carrier}
    (hx : x ∈ ((F.event T hT).necks i).neck.region
      (-((F.event T hT).necks i).neck.epsilon⁻¹) 0)
    (v w : TangentSpace (𝓡 3) x) :
    let top := (F.event T hT).retention.map ∘ (F.event T hT).limit_identify.inverse
    (F.metric T).inner (top x)
      (mfderiv (𝓡 3) (𝓡 3) top x v) (mfderiv (𝓡 3) (𝓡 3) top x w) =
        (F.event T hT).limit_metric.inner x v w := by
  let event := F.event T hT
  have hpre := source_negative_neck_interior_retained hT i hx
  have hreg := event.retained_pre_subset (interior_subset hpre)
  have hinv := (event.limit_identify.inverse_smooth.contMDiffAt
    (by simp : (univ : Set event.terminal.carrier) ∈ 𝓝 x)).mdifferentiableAt (by simp)
  have hret := (event.retention.map_smooth.contMDiffAt
    (mem_interior_iff_mem_nhds.mp hpre)).mdifferentiableAt (by simp)
  have hlim := (event.limit_identify.map_smooth.contMDiffAt
    (event.regular_limit_open.mem_nhds hreg)).mdifferentiableAt (by simp)
  have heq : event.limit_identify.map ∘ event.limit_identify.inverse =ᶠ[𝓝 x] id :=
    Filter.Eventually.of_forall (fun y => event.limit_identify.right_inverse (mem_univ y))
  have hderiv := (mfderiv_comp x hlim hinv).symm.trans heq.mfderiv_eq
  have hv := congrArg (fun L => L v) hderiv
  have hw := congrArg (fun L => L w) hderiv
  simp only [mfderiv_id] at hv hw
  change mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (event.limit_identify.inverse x)
    (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.inverse x v) = v at hv
  change mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (event.limit_identify.inverse x)
    (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.inverse x w) = w at hw
  have hm := event.retained_metric (event.limit_identify.inverse x) (interior_subset hpre)
    (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.inverse x v)
    (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.inverse x w)
  rw [hv, hw] at hm
  rw [event.limit_identify.right_inverse (mem_univ x)] at hm
  change (F.metric T).inner _ (mfderiv (𝓡 3) (𝓡 3)
    (event.retention.map ∘ event.limit_identify.inverse) x v)
    (mfderiv (𝓡 3) (𝓡 3) (event.retention.map ∘ event.limit_identify.inverse) x w) = _
  rw [mfderiv_comp x hret hinv]
  exact hm



theorem source_initial_closed_zero_metric
    {F : SurgeryFlowData.{u}} {T q : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    {I : Set ℝ} {V : Set (F.event T hT).terminal.carrier}
    (e : SurgeryFlowCylinder F (F.event T hT).terminal T q I V)
    (hzero : (0 : ℝ) ∈ I)
    (hmap : ∀ x, HEq (e.forward 0 hzero x)
      ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x)))
    {x : (F.event T hT).terminal.carrier}
    (hx : x ∈ ((F.event T hT).necks i).neck.region
      (-((F.event T hT).necks i).neck.epsilon⁻¹) 0)
    (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner 0 hzero x v w = q * (F.event T hT).limit_metric.inner x v w := by
  let top := (F.event T hT).retention.map ∘ (F.event T hT).limit_identify.inverse
  have hSigma : (⟨T + 0 / q, e.forward 0 hzero⟩ :
      (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier)) = ⟨T, top⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    apply Function.hfunext rfl
    intro y z hyz
    cases hyz
    exact hmap y
  have hread := congrArg
    (fun p : (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier) =>
      q * (F.metric p.1).inner (p.2 x)
        (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hSigma
  exact hread.trans (congrArg (q * ·) (source_initial_retained_limit_metric hT i hx v w))

private theorem retainedTensor_metric_agreement
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I J : Set ℝ} {U V : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : SurgeryFlowCylinder F C origin scale J V) (hU : IsOpen U)
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



theorem source_initial_older_tensor_on_closed_cylinder
    {F : SurgeryFlowData.{u}} {T left : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    (old : SurgeryTerminalStrongNeck F T hT i)
    {U V : Set (F.event T hT).terminal.carrier}
    (D : SurgeryFlowCylinder F (F.event T hT).terminal T
      (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Icc left (-1 / 2)) U)
    (e : SurgeryFlowCylinder F (F.event T hT).terminal T
      (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Icc left 0) V)
    (hV : IsOpen V)
    (hnegative : V ⊆ ((F.event T hT).necks i).neck.region
      (-((F.event T hT).necks i).neck.epsilon⁻¹) 0)
    (hpast : ∀ s (hs : s ∈ Icc left (-1 / 2)) (hs' : s ∈ Icc left 0),
      ∀ x ∈ V, e.forward s hs' x = D.forward s hs x)
    (hold : ∀ s (hs : s ∈ Ioo (-1 : ℝ) 0) (hs' : s ∈ Icc left 0),
      ∀ x ∈ V, e.forward s hs' x = old.cylinder.forward s hs x)
    (hzero : ∀ hs x, HEq (e.forward 0 hs x)
      ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x)))
    (s : ℝ) (hs : s ∈ Icc left 0) (z : RoundCylinderSpace)
    (hz : ((F.event T hT).necks i).neck.coordinate_map z ∈ V)
    (v w : RoundCylinderTangent z) :
    sourceInitialOlderTensor old D s z v w =
      surgeryCylinderPullback e ((F.event T hT).necks i).neck.coordinate_map s z v w := by
  let N := ((F.event T hT).necks i).neck
  by_cases hp : s ≤ -1
  · have hsD : s ∈ Icc left (-1 / 2) := ⟨hs.1, by linarith only [hp]⟩
    have hm := retainedTensor_metric_agreement e D hV hs hsD (hpast s hsD hs) hz
      (mfderiv Ic (𝓡 3) N.coordinate_map z v) (mfderiv Ic (𝓡 3) N.coordinate_map z w)
    simpa only [sourceInitialOlderTensor, if_pos hp, surgeryCylinderPullback,
      dif_pos hsD, dif_pos hs, SurgeryFlowCylinder.pullbackInner, N] using hm.symm
  · by_cases hs0 : s = 0
    · subst s
      have hm := source_initial_closed_zero_metric hT i e hs (hzero hs) (hnegative hz)
        (mfderiv Ic (𝓡 3) N.coordinate_map z v) (mfderiv Ic (𝓡 3) N.coordinate_map z w)
      simpa only [sourceInitialOlderTensor, if_neg hp, if_true, roundCylinderPullback,
        surgeryCylinderPullback, dif_pos hs, SurgeryFlowCylinder.pullbackInner, N] using hm.symm
    · have hsOld : s ∈ Ioo (-1 : ℝ) 0 := ⟨lt_of_not_ge hp, lt_of_le_of_ne hs.2 hs0⟩
      have hm := retainedTensor_metric_agreement e old.cylinder hV hs hsOld
        (hold s hsOld hs) hz (mfderiv Ic (𝓡 3) N.coordinate_map z v)
        (mfderiv Ic (𝓡 3) N.coordinate_map z w)
      simpa only [sourceInitialOlderTensor, if_neg hp, if_neg hs0, surgeryCylinderPullback,
        dif_pos hsOld, dif_pos hs, SurgeryFlowCylinder.pullbackInner, N] using hm.symm



theorem source_initial_cylinder_affine_pullback
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (lambda c s : ℝ) (hs : s ∈ I) {z : RoundCylinderSpace}
    (hz : lambda * z.2 + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    surgeryCylinderPullback e (N.coordinate_map ∘ neckAxialSpaceMap lambda c) s z v w =
      neckAxialTensorPullback lambda c (surgeryCylinderPullback e N.coordinate_map s) z v w := by
  have hN := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show neckAxialSpaceMap lambda c z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hz⟩))).mdifferentiableAt (by simp)
  have hA : MDifferentiableAt Ic Ic (neckAxialSpaceMap lambda c) z :=
    (neckAxialSpaceMap_contMDiff lambda c).contMDiffAt.mdifferentiableAt (by simp)
  simp only [surgeryCylinderPullback, dif_pos hs, neckAxialTensorPullback,
    mfderiv_comp z hN hA, ContinuousLinearMap.comp_apply,
    neckAxialSpaceMap_mfderiv, Function.comp_apply]

end PoincareConjecture.M47
