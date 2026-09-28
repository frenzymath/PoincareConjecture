import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PinchingBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_SlabScalarTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

theorem slice_nonempty_of_later (F : SurgeryFlowData.{u}) {s t : ℝ}
    (hs : s ∈ F.time_domain) (ht : t ∈ F.time_domain) (hst : s ≤ t)
    [Nonempty (F.slice t).carrier] : Nonempty (F.slice s).carrier := by
  by_contra h
  let hempty : IsEmpty (F.slice s).carrier := ⟨fun x => h ⟨x⟩⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty (F.slice t).carrier)
  exact (F.extinction_permanent s t hs ht hst hempty).false x

theorem curvature_unbounded_before_surgery (F : SurgeryFlowData.{u})
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (L s : ℝ) (hs : s < T) :
    ∃ t ∈ Ioo s T, ∃ x : (F.slice t).carrier, L < (F.connection t).curvatureTensorNorm x := by
  classical
  have hdomain := F.surgery_times_subset hT
  have hnonneg := F.time_domain_nonnegative hdomain
  have hpos : 0 < T := lt_of_le_of_ne hnonneg (by
    intro hzero
    exact F.zero_not_surgery (hzero ▸ hT))
  have hprefix : Icc 0 T ⊆ F.time_domain := F.time_domain_interval.out F.zero_mem hdomain
  let times := insert 0 (F.surgery_times ∩ Ioo 0 T)
  have hfinite : times.Finite :=
    ((F.surgery_times_finite_on_compact isCompact_Icc hprefix).subset
      (inter_subset_inter_right _ Ioo_subset_Icc_self)).insert 0
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image times (fun x : ℝ => x) hfinite
    ⟨0, mem_insert _ _⟩
  have hab : 0 ≤ a ∧ a < T ∧ (a = 0 ∨ a ∈ F.surgery_times) := by
    rcases ha with ha | ha
    · exact ⟨by simp [ha], by simpa [ha] using hpos, Or.inl ha⟩
    · exact ⟨ha.2.1.le, ha.2.2, Or.inr ha.1⟩
  have haDomain := hprefix ⟨hab.1, hab.2.1.le⟩
  have hinterval : Ico a T ⊆ F.time_domain :=
    fun _ ht => hprefix ⟨hab.1.trans ht.1, ht.2.le⟩
  have hfree : Disjoint F.surgery_times (Ioo a T) := by
    apply Set.disjoint_left.mpr
    intro t ht hta
    have hmem : t ∈ times := mem_insert_of_mem 0 ⟨ht, hab.1.trans_lt hta.1, hta.2⟩
    exact (not_lt_of_ge (hmax t hmem)) hta.1
  let := slice_nonempty_of_later F haDomain hdomain hab.2.1.le
  obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals a T haDomain hab.2.2 hab.2.1
    hinterval hfree (Or.inl hT) L s hs
  exact ⟨t, ⟨(le_max_right a s).trans_lt ht.1, ht.2⟩, x, hx⟩

theorem event_preterminal_surgery_free (P : M44CapPersistencePredecessors.{u})
    (F : SurgeryFlowData.{u}) (hpinch : SurgeryFlowPinched F)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] :
    Disjoint F.surgery_times (Ioo (F.event T hT).tMinus T) := by
  let event := F.event T hT
  have hdomain := F.surgery_times_subset hT
  have hprefix : Icc 0 T ⊆ F.time_domain := F.time_domain_interval.out F.zero_mem hdomain
  have hminus : event.tMinus ∈ F.time_domain :=
    hprefix ⟨event.tMinus_nonnegative, event.tMinus_lt.le⟩
  apply Set.disjoint_left.mpr
  intro S hS hSI
  have hSdomain := F.surgery_times_subset hS
  let := slice_nonempty_of_later F hSdomain hdomain hSI.2.le
  let c := (event.tMinus + S) / 2
  have hc : event.tMinus < c ∧ c < S := by dsimp [c]; constructor <;> linarith [hSI.1]
  have hrect : Icc c S ×ˢ (univ : Set (F.slice event.tMinus).carrier) ⊆
      Ico event.tMinus T ×ˢ univ :=
    fun _ hp => ⟨⟨hc.1.le.trans hp.1.1, hp.1.2.trans_lt hSI.2⟩, hp.2⟩
  have hcompact : IsCompact (Icc c S ×ˢ (univ : Set (F.slice event.tMinus).carrier)) :=
    isCompact_Icc.prod (F.slices_compact event.tMinus hminus)
  have hscalar : ContinuousOn
      (fun p : ℝ × (F.slice event.tMinus).carrier =>
        (event.pre_flow.connection p.1).scalarCurvature p.2) (Icc c S ×ˢ univ) :=
    (P.curvature.scalar_regular 3 (F.slice event.tMinus).carrier
      (Ico event.tMinus T) event.pre_flow).continuousOn.mono hrect
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hscalar
  have hbound (t : ℝ) (ht : t ∈ Icc c S) (x : (F.slice t).carrier) :
      (F.connection t).curvatureTensorNorm x ≤ 13 * max B (Real.exp 4) := by
    have htime : t ∈ Ico event.tMinus T :=
      ⟨hc.1.le.trans ht.1, ht.2.trans_lt hSI.2⟩
    let q := (event.pre_identify ⟨t, htime⟩).symm x
    have hhom : MetricHomothety (event.pre_flow.metric t) (F.metric t)
        (event.pre_identify ⟨t, htime⟩) 1 := by
      intro y v w
      simpa only [one_mul] using event.pre_metric ⟨t, htime⟩ y v w
    have heq := M13.homothety_scalarCurvature_eq _ _ _ 1 zero_lt_one hhom
      (event.pre_flow.connection t) (F.connection t) q
    have hscalarBound : (F.connection t).scalarCurvature x ≤ B := by
      have h := hB (mem_image_of_mem _ (show (t, q) ∈
        Icc c S ×ˢ (univ : Set (F.slice event.tMinus).carrier) from ⟨ht, mem_univ _⟩))
      have heqx : (F.connection t).scalarCurvature x =
          (event.pre_flow.connection t).scalarCurvature q := by
        simpa only [q, Diffeomorph.apply_symm_apply, div_one] using heq
      exact heqx.trans_le h
    have hnorm := (hpinch t
      (hprefix ⟨event.tMinus_nonnegative.trans htime.1, htime.2.le⟩)).curvature_norm_le
        P (mem_univ x)
    exact hnorm.trans
        (mul_le_mul_of_nonneg_left (max_le_max_right _ hscalarBound) (by norm_num))
  obtain ⟨t, ht, x, hx⟩ := curvature_unbounded_before_surgery F hS
    (13 * max B (Real.exp 4)) c hc.2
  exact (not_lt_of_ge (hbound t ⟨ht.1.le, ht.2.le⟩ x)) hx

end PoincareConjecture.M44
