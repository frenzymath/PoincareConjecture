import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalar
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Algebra.Order.Group.OrderIso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

theorem cylinderScalar_tendsto_left_at_surgery
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {C : GeneralizedSliceCarrier.{u}} {origin scale c : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) {s : ℝ} (hs : s ∈ Ioc c 0)
    (hT : origin + s / scale ∈ F.surgery_times) :
    Tendsto (cylinderScalar e x) (𝓝[<] s) (𝓝 (cylinderScalar e x s)) := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  let : Nonempty (F.slice (origin + s / scale)).carrier :=
    ⟨e.forward s ⟨hs.1.le, hs.2⟩ x⟩
  let event := F.event (origin + s / scale) hT
  obtain ⟨v, hv, hvs⟩ := exists_between
    (max_lt (clock.strictMono hs.1) event.tMinus_lt)
  let r := clock.symm v
  have hcr : c < r := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using (le_max_left _ _).trans_lt hv
  have hrs : r < s := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using hvs
  have hr : r ∈ Icc c 0 := ⟨hcr.le, hrs.le.trans hs.2⟩
  have hr' : origin + r / scale ∈ Ico event.tMinus (origin + s / scale) := by
    change clock r ∈ Ico event.tMinus (clock s)
    simpa only [r, OrderIso.apply_symm_apply] using
      (show v ∈ Ico event.tMinus (clock s) from ⟨((le_max_right _ _).trans_lt hv).le, hvs⟩)
  let z := (event.pre_identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)
  have hz : z ∈ interior event.retained_pre :=
    e.pre_retained_at_surgery s ⟨hs.1.le, hs.2⟩ hT r hr hr' x hx
  have hmap : event.retention.map z = e.forward s ⟨hs.1.le, hs.2⟩ x :=
    e.surgery_compatibility s ⟨hs.1.le, hs.2⟩ hT r hr hr' x hx
  have hclock : Tendsto clock (𝓝[<] s) (𝓝[<] (clock s)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨clock.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact clock.strictMono ht
  have hlimit := (tendsto_preterminal_scalar_retained event
    (F.connection (origin + s / scale)) hz).comp hclock
  rw [hmap, ← cylinderScalar_of_mem e x s ⟨hs.1.le, hs.2⟩] at hlimit
  apply hlimit.congr'
  filter_upwards [Ioo_mem_nhdsLT hrs] with t ht
  have htI : t ∈ Icc c 0 := ⟨(hcr.trans ht.1).le, ht.2.le.trans hs.2⟩
  have ht' : origin + t / scale ∈ Ico event.tMinus (origin + s / scale) :=
    ⟨hr'.1.trans (clock.monotone ht.1.le), clock.strictMono ht.2⟩
  exact (cylinderScalar_eq_preterminal P hpinch e hx hT r t hr htI hr' ht').symm

end PoincareConjecture.Proofs.M46
