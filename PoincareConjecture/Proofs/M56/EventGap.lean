import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy
import PoincareConjecture.Proofs.M13.MetricCalculus
import PoincareConjecture.Proofs.M51.EventMaximality












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



theorem m56Slice_nonempty_of_le (F : SurgeryFlowData.{u})
    {s t : ℝ} (hs : s ∈ F.time_domain) (ht : t ∈ F.time_domain)
    (hst : s ≤ t) (hne : Nonempty (F.slice t).carrier) :
    Nonempty (F.slice s).carrier := by
  by_contra h
  obtain ⟨x⟩ := hne
  exact (F.extinction_permanent s t hs ht hst ⟨fun y => h ⟨y⟩⟩).false x



theorem m56Event_gap (F : SurgeryFlowData.{u}) {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
    Disjoint F.surgery_times (Ioo (F.event T hT).tMinus T) := by
  apply Set.disjoint_left.mpr
  intro S hS hST
  let E := F.event T hT
  have hEtime : E.tMinus ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
      ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
  let : Nonempty (F.slice S).carrier := m56Slice_nonempty_of_le F
    (F.surgery_times_subset hS) (F.surgery_times_subset hT) hST.2.le inferInstance
  obtain ⟨a, ha, hstart, haS, hI, hfree, hne⟩ := F.lastRegularStart hS
  let : Nonempty (F.slice a).carrier := hne
  let b := (E.tMinus + S) / 2
  have hEb : E.tMinus < b := by dsimp [b]; linarith [hST.1]
  have hbS : b < S := by dsimp [b]; linarith [hST.1]
  have hsub : Icc b S ×ˢ (univ : Set (F.slice E.tMinus).carrier) ⊆
      Ico E.tMinus T ×ˢ univ := by
    intro p hp
    exact ⟨⟨hEb.le.trans hp.1.1, hp.1.2.trans_lt hST.2⟩, hp.2⟩
  have hcont := (M04.contMDiffOn_flow_curvatureDerivativeEnergy E.pre_flow 0).continuousOn
  have hcompact := (isCompact_Icc : IsCompact (Icc b S)).prod
    (F.slices_compact E.tMinus hEtime)
  obtain ⟨L, hL⟩ := hcompact.bddAbove_image (hcont.mono hsub)
  obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals a S ha hstart haS hI hfree
    (Or.inl hS) (|L| + 1) b hbS
  have hbt : b < t := (le_max_right a b).trans_lt ht.1
  have htpre : t ∈ Ico E.tMinus T := ⟨hEb.le.trans hbt.le, ht.2.trans hST.2⟩
  let e := E.pre_identify ⟨t, htpre⟩
  have hmetric : MetricHomothety (E.pre_flow.metric t) (F.metric t) e 1 := by
    intro y v w
    simpa only [one_mul] using E.pre_metric ⟨t, htpre⟩ y v w
  have hnorm := (M13.metricHomothetyCalculus (E.pre_flow.metric t)
    (F.metric t) e 1 (by norm_num) hmetric).curvature_norm_eq
      (E.pre_flow.connection t) (F.connection t) (e.symm x)
  rw [e.apply_symm_apply, div_one] at hnorm
  have hsq := hL ⟨(t, e.symm x), ⟨⟨hbt.le, ht.2.le⟩, mem_univ _⟩, rfl⟩
  change (E.pre_flow.connection t).curvatureDerivativeNorm 0 (e.symm x) ^ 2 ≤ L at hsq
  rw [LeviCivitaData.curvatureDerivativeNorm_zero] at hsq
  rw [← hnorm] at hsq
  have hLabs : L ≤ |L| := le_abs_self L
  have hnonneg : 0 ≤ |L| := abs_nonneg L
  nlinarith [sq_nonneg ((F.connection t).curvatureTensorNorm x - 1)]

end PoincareConjecture
