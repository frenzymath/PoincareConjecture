import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMetric
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_PhysicalBirthMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin : ℝ} {I : Set ℝ} {U : Set C.carrier}

noncomputable def cylinderQuadratic
    (e : SurgeryFlowCylinder F C origin 1 I U) (x : C.carrier)
    (v : TangentSpace (𝓡 3) x) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then e.pullbackInner s hs x v v else 0

theorem cylinderQuadratic_of_mem (e : SurgeryFlowCylinder F C origin 1 I U)
    (x : C.carrier) (v : TangentSpace (𝓡 3) x) (s : ℝ) (hs : s ∈ I) :
    cylinderQuadratic e x v s = (F.metric (origin + s / 1)).inner (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) := by
  classical
  simp only [cylinderQuadratic, dif_pos hs, SurgeryFlowCylinder.pullbackInner, one_mul]

theorem cylinderQuadratic_eq_slab
    (e : SurgeryFlowCylinder F C origin 1 I U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (r s : ℝ) (hr : r ∈ I) (hs : s ∈ I)
    (hr' : origin + r / 1 ∈ Icc a b) (hs' : origin + s / 1 ∈ Icc a b) :
    let S := F.regular_slabs a b hab hJ hfree
    let f := (S.identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
    cylinderQuadratic e x v s = (S.flow.metric (origin + s / 1)).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
  dsimp only
  let S := F.regular_slabs a b hab hJ hfree
  let f := (S.identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x :=
    (S.identify ⟨origin + r / 1, hr'⟩).symm.contMDiff.contMDiffAt.comp x
      ((e.forward_smooth r hr).contMDiffAt (hU.mem_nhds hx))
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (S.identify ⟨origin + s / 1, hs'⟩) (f x) :=
    (S.identify ⟨origin + s / 1, hs'⟩).contMDiff.contMDiffAt
  have hnear : e.forward s hs =ᶠ[𝓝 x] (S.identify ⟨origin + s / 1, hs'⟩) ∘ f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (e.slab_compatibility a b hab hJ hfree r hr s hs hr' hs' y hy).symm
  rw [cylinderQuadratic_of_mem e x v s hs, hnear.mfderiv_eq, hnear.eq_of_nhds,
    mfderiv_comp x (hi.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact S.metric_pullback ⟨origin + s / 1, hs'⟩ (f x) _ _

theorem cylinderQuadratic_eq_preterminal
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin 1 I U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (r s : ℝ) (hr : r ∈ I) (hs : s ∈ I)
    (hr' : origin + r / 1 ∈ Ico (F.event T hT).tMinus T)
    (hs' : origin + s / 1 ∈ Ico (F.event T hT).tMinus T) :
    let event := F.event T hT
    let f := (event.pre_identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
    cylinderQuadratic e x v s = (event.pre_flow.metric (origin + s / 1)).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
  dsimp only
  let event := F.event T hT
  let f := (event.pre_identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x :=
    (event.pre_identify ⟨origin + r / 1, hr'⟩).symm.contMDiff.contMDiffAt.comp x
      ((e.forward_smooth r hr).contMDiffAt (hU.mem_nhds hx))
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (event.pre_identify ⟨origin + s / 1, hs'⟩) (f x) :=
    (event.pre_identify ⟨origin + s / 1, hs'⟩).contMDiff.contMDiffAt
  have hnear : e.forward s hs =ᶠ[𝓝 x] (event.pre_identify ⟨origin + s / 1, hs'⟩) ∘ f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have h := M44.cylinder_preterminal_coordinates_eq_of_pinched P hpinch e
      hT s hs r hr hs' hr' y hy
    have hmap := congrArg (event.pre_identify ⟨origin + s / 1, hs'⟩) h
    dsimp only [event] at hmap
    simpa only [Diffeomorph.apply_symm_apply, f, event, Function.comp_apply] using hmap
  rw [cylinderQuadratic_of_mem e x v s hs, hnear.mfderiv_eq, hnear.eq_of_nhds,
    mfderiv_comp x (hi.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact event.pre_metric ⟨origin + s / 1, hs'⟩ (f x) _ _

theorem cylinderQuadratic_eq_retained_terminal
    (e : SurgeryFlowCylinder F C origin 1 I U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    (s : ℝ) (hs : s ∈ I) (hT : origin + s / 1 ∈ F.surgery_times)
    [Nonempty (F.slice (origin + s / 1)).carrier]
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / 1 ∈ Ico (F.event (origin + s / 1) hT).tMinus (origin + s / 1)) :
    let event := F.event (origin + s / 1) hT
    let f := (event.pre_identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
    cylinderQuadratic e x v s = event.limit_metric.inner (event.limit_identify.map (f x))
      (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v))
      (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.map (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v)) := by
  dsimp only
  let event := F.event (origin + s / 1) hT
  let f := (event.pre_identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
  have hret : f x ∈ interior event.retained_pre :=
    e.pre_retained_at_surgery s hs hT r hr hr' x hx
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x :=
    (event.pre_identify ⟨origin + r / 1, hr'⟩).symm.contMDiff.contMDiffAt.comp x
      ((e.forward_smooth r hr).contMDiffAt (hU.mem_nhds hx))
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ event.retention.map (f x) :=
    (event.retention.map_smooth.mono interior_subset).contMDiffAt
      (isOpen_interior.mem_nhds hret)
  have hnear : e.forward s hs =ᶠ[𝓝 x] event.retention.map ∘ f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (e.surgery_compatibility s hs hT r hr hr' y hy).symm
  rw [cylinderQuadratic_of_mem e x v s hs, hnear.mfderiv_eq, hnear.eq_of_nhds,
    mfderiv_comp x (hi.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact event.retained_metric (f x) (interior_subset hret) _ _

end PoincareConjecture.Proofs.M46
