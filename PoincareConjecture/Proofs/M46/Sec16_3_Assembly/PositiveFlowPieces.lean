import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.TerminalSectionalLowerBound
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveSurgeryMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

open M04

theorem positive_component_regular_transport
    (F : SurgeryFlowData.{u}) {a b : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : Icc a b) (hst : s.1 ≤ t.1) (x : (F.slice s.1).carrier)
    (hpos : SurgeryPositiveComponentAt F s.1 x) :
    SurgeryPositiveComponentAt F t.1
      ((F.regular_slabs a b hab hI hfree).transport s t x) := by
  let slab := F.regular_slabs a b hab hI hfree
  let : CompactSpace (F.slice a).carrier :=
    isCompact_univ_iff.mp (F.slices_compact a (hI ⟨le_rfl, hab.le⟩))
  let z := (slab.identify s).symm x
  have hstart : ∀ y ∈ connectedComponent z, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (slab.flow.metric s.1) y u v →
        0 < (slab.flow.connection s.1).sectionalCurvature y u v := by
    apply (component_positive_iff_of_diffeomorph (slab.flow.connection s.1)
      (F.connection s.1) (slab.identify s)
      (fun y u v => (slab.metric_pullback s y u v).symm) z).mpr
    simpa only [z, Diffeomorph.apply_symm_apply, SurgeryPositiveComponentAt] using hpos
  obtain ⟨c, hc, hbound⟩ := positive_sectional_uniform_on_component
    slab.flow s.2 z hstart
  have hterminal : ∀ y ∈ connectedComponent z, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (slab.flow.metric t.1) y u v →
        0 < (slab.flow.connection t.1).sectionalCurvature y u v := by
    intro y hy u v hpair
    have h := hbound t.1 t.2 hst y hy u v
    simp only [metricGram, hpair.1, hpair.2.1, hpair.2.2,
      zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one] at h
    simpa only [LeviCivitaData.sectionalCurvature, hpair.1, hpair.2.1, hpair.2.2,
      one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using hc.trans_le h
  exact (component_positive_iff_of_diffeomorph (slab.flow.connection t.1)
    (F.connection t.1) (slab.identify t)
    (fun y u v => (slab.metric_pullback t y u v).symm) z).mp hterminal

theorem positive_component_surgery_from_reference
    (F : SurgeryFlowData.{u}) {T : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (v : Ico (F.event T hT).tMinus T)
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hpos : SurgeryPositiveComponentAt F v.1 ((F.event T hT).pre_identify v x)) :
    ∀ q ∈ (F.event T hT).retained_pre ∩ connectedComponent x,
      SurgeryPositiveComponentAt F T ((F.event T hT).retention.map q) := by
  let event := F.event T hT
  have htm : event.tMinus ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
      ⟨event.tMinus_nonnegative, event.tMinus_lt.le⟩
  let : CompactSpace (F.slice event.tMinus).carrier :=
    isCompact_univ_iff.mp (F.slices_compact event.tMinus htm)
  let : LocallyConnectedSpace (F.slice event.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  have hstart : ∀ y ∈ connectedComponent x, ∀ u w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (event.pre_flow.metric v.1) y u w →
        0 < (event.pre_flow.connection v.1).sectionalCurvature y u w :=
    (component_positive_iff_of_diffeomorph (event.pre_flow.connection v.1)
      (F.connection v.1) (event.pre_identify v)
      (fun y u w => (event.pre_metric v y u w).symm) x).mpr hpos
  obtain ⟨c, hc, hbound⟩ := positive_sectional_uniform_on_component
    event.pre_flow v.2 x hstart
  have hterminal : ∀ q ∈ connectedComponent x, q ∈ event.regular_limit →
      ∀ u w : TangentSpace (𝓡 3) (event.limit_identify.map q),
        LeviCivitaData.IsOrthonormalPair event.limit_metric (event.limit_identify.map q) u w →
          0 < event.limit_connection.sectionalCurvature (event.limit_identify.map q) u w := by
    intro q hq hreg
    apply terminal_sectional_positive_of_preterminal event hreg hc
    filter_upwards [Ico_mem_nhdsLT v.2.2] with t ht
    exact hbound t ⟨v.2.1.trans ht.1, ht.2⟩ ht.1 q hq
  intro q hq
  exact positive_sectional_child_component event (F.connection T)
    isClopen_connectedComponent hterminal hq

end PoincareConjecture.Proofs.M46
