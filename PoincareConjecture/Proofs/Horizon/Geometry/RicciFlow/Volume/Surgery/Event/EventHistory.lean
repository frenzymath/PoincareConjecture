import PoincareConjecture.Proofs.M49.Lemma17_12_EventHistory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Volume.LossData

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.SurgeryVolume

variable (F : SurgeryFlowData.{u})

theorem initialInterval_subset {T : ℝ} (hT : T ∈ F.time_domain) :
    Icc 0 T ⊆ F.time_domain :=
  F.time_domain_interval.out F.zero_mem hT

theorem surgeryTime_pos {T : ℝ} (hT : T ∈ F.surgery_times) : 0 < T := by
  have hnonneg : 0 ≤ T := F.time_domain_nonnegative (F.surgery_times_subset hT)
  exact lt_of_le_of_ne hnonneg (fun h => F.zero_not_surgery (h.symm ▸ hT))

theorem nonemptyEventPreInterval : RepairedNonemptyEventPreInterval F := by
  intro T hT hN t ht
  exact initialInterval_subset F (F.surgery_times_subset hT)
    ⟨(F.event T hT).tMinus_nonnegative.trans ht.1, ht.2.le⟩

theorem vanishingEventPreInterval : RepairedVanishingEventPreInterval F := by
  intro T hT hE t ht
  exact initialInterval_subset F (F.surgery_times_subset hT)
    ⟨(F.vanishing_event T hT).tMinus_nonnegative.trans ht.1, ht.2.le⟩

theorem surgeryTimes_inter_finite {K : Set ℝ} (hK : IsCompact K)
    (hKD : K ⊆ F.time_domain) : (F.surgery_times ∩ K).Finite := by
  apply hK.induction_on (p := fun U => (F.surgery_times ∩ U).Finite)
  · simp
  · intro U V hUV hV
    exact hV.subset (inter_subset_inter_right _ hUV)
  · intro U V hU hV
    simpa only [inter_union_distrib_left] using hU.union hV
  · intro t ht
    obtain ⟨d, hd, hfinite⟩ := F.surgery_times_locally_finite t (hKD ht)
    refine ⟨Ioo (t - d) (t + d), mem_nhdsWithin_of_mem_nhds ?_, hfinite⟩
    exact Ioo_mem_nhds (by linarith) (by linarith)

theorem surgeryTimes_inter_Icc_finite {a b : ℝ}
    (ha : a ∈ F.time_domain) (hb : b ∈ F.time_domain) :
    (F.surgery_times ∩ Icc a b).Finite :=
  surgeryTimes_inter_finite F isCompact_Icc (F.time_domain_interval.out ha hb)

theorem nonempty_before_vanishing {T : ℝ} (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] {s : ℝ} (hs : s ∈ F.time_domain) (hsT : s < T) :
    Nonempty (F.slice s).carrier := by
  classical
  by_contra hN
  let : IsEmpty (F.slice s).carrier := not_nonempty_iff.mp hN
  let E := F.vanishing_event T hT
  let t := max s E.tMinus
  have ht : t ∈ Ico E.tMinus T := ⟨le_max_right _ _, max_lt hsT E.tMinus_lt⟩
  have htD : t ∈ F.time_domain := vanishingEventPreInterval F T hT ht
  let : IsEmpty (F.slice t).carrier :=
    F.extinction_permanent s t hs htD (le_max_left _ _) inferInstance
  obtain ⟨x⟩ := E.pre_nonempty
  exact isEmptyElim (E.pre_identify ⟨t, ht⟩ x)

theorem vanishingTimes_subsingleton :
    {T ∈ F.surgery_times | IsEmpty (F.slice T).carrier}.Subsingleton := by
  intro s hs t ht
  rcases lt_trichotomy s t with hst | hst | hts
  · let := hs.2
    let := ht.2
    obtain ⟨x⟩ := nonempty_before_vanishing F ht.1 (F.surgery_times_subset hs.1) hst
    exact isEmptyElim x
  · exact hst
  · let := hs.2
    let := ht.2
    obtain ⟨x⟩ := nonempty_before_vanishing F hs.1 (F.surgery_times_subset ht.1) hts
    exact isEmptyElim x

theorem vanishingVolumeData (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] : RepairedVanishingVolumeData F T hT where
  post_volume_zero := by rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty]
  volume_drop := by
    rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty]
    exact bot_le

end PoincareConjecture.SurgeryVolume
