import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetric
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Algebra.Order.Group.OrderIso









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem cylinderQuadratic_tendsto_left_at_surgery
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {C : GeneralizedSliceCarrier.{u}} {origin c : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin 1 (Icc c 0) U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {s : ℝ} (hs : s ∈ Ioc c 0) (hT : origin + s / 1 ∈ F.surgery_times) :
    Tendsto (cylinderQuadratic e x v) (𝓝[<] s) (𝓝 (cylinderQuadratic e x v s)) := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ 1 e.scale_pos).trans (OrderIso.addLeft origin)
  let : Nonempty (F.slice (origin + s / 1)).carrier :=
    ⟨e.forward s ⟨hs.1.le, hs.2⟩ x⟩
  let event := F.event (origin + s / 1) hT
  obtain ⟨b, hb, hbs⟩ := exists_between
    (max_lt (clock.strictMono hs.1) event.tMinus_lt)
  let r := clock.symm b
  have hcr : c < r := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using (le_max_left _ _).trans_lt hb
  have hrs : r < s := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using hbs
  have hr : r ∈ Icc c 0 := ⟨hcr.le, hrs.le.trans hs.2⟩
  have hr' : origin + r / 1 ∈ Ico event.tMinus (origin + s / 1) := by
    change clock r ∈ Ico event.tMinus (clock s)
    simpa only [r, OrderIso.apply_symm_apply] using
      (show b ∈ Ico event.tMinus (clock s) from ⟨((le_max_right _ _).trans_lt hb).le, hbs⟩)
  let f := (event.pre_identify ⟨origin + r / 1, hr'⟩).symm ∘ e.forward r hr
  have hret : f x ∈ interior event.retained_pre :=
    e.pre_retained_at_surgery s ⟨hs.1.le, hs.2⟩ hT r hr hr' x hx
  have hclock : Tendsto clock (𝓝[<] s) (𝓝[<] (clock s)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨clock.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact clock.strictMono ht
  have hlimit := (M44.tendsto_preterminal_metric_inner event
    (event.retained_pre_subset (interior_subset hret))
    (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v)).comp hclock
  have hendpoint := cylinderQuadratic_eq_retained_terminal e hU hx v s
    ⟨hs.1.le, hs.2⟩ hT r hr hr'
  rw [← hendpoint] at hlimit
  apply hlimit.congr'
  filter_upwards [Ioo_mem_nhdsLT hrs] with t ht
  have htI : t ∈ Icc c 0 := ⟨(hcr.trans ht.1).le, ht.2.le.trans hs.2⟩
  have ht' : origin + t / 1 ∈ Ico event.tMinus (origin + s / 1) :=
    ⟨hr'.1.trans (clock.monotone ht.1.le), clock.strictMono ht.2⟩
  exact (cylinderQuadratic_eq_preterminal P hpinch e hU hx v hT r t hr htI hr' ht').symm

end PoincareConjecture.Proofs.M46
