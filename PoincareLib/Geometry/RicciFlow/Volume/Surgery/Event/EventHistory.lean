import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Lemma17_12_EventHistory.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Event history for the volume-counting argument

Morgan-Tian, Lemma 17.12, pp. 410-411, uses finite included prefixes and
counts disappearance of components. Here the raw interval and extinction
axioms give the predecessor intervals, finite compact event sets, and at
most one vanishing event. See `proof-work/tasks/M49/derivations/01-foundations.md`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace PoincareMT.SurgeryVolume

variable (F : SurgeryFlowData.{u})

/-- The included initial segment used in Lemma 17.12, p. 410, lies in the raw domain. -/
theorem initialInterval_subset {T : ℝ} (hT : T ∈ F.time_domain) :
    Icc 0 T ⊆ F.time_domain :=
  F.time_domain_interval.out F.zero_mem hT

/-- Surgery times in Lemma 17.12, p. 410, are strictly after the initial slice. -/
theorem surgeryTime_pos {T : ℝ} (hT : T ∈ F.surgery_times) : 0 < T := by
  have hnonneg : 0 ≤ T := F.time_domain_nonnegative (F.surgery_times_subset hT)
  exact lt_of_le_of_ne hnonneg (fun h => F.zero_not_surgery (h.symm ▸ hT))

/-- Nonempty event predecessor intervals are included, as used in Lemma 17.12, p. 410. -/
theorem nonemptyEventPreInterval : RepairedNonemptyEventPreInterval F := by
  intro T hT hN t ht
  exact initialInterval_subset F (F.surgery_times_subset hT)
    ⟨(F.event T hT).tMinus_nonnegative.trans ht.1, ht.2.le⟩

/-- Vanishing event predecessor intervals are included, as used in Lemma 17.12, p. 410. -/
theorem vanishingEventPreInterval : RepairedVanishingEventPreInterval F := by
  intro T hT hE t ht
  exact initialInterval_subset F (F.surgery_times_subset hT)
    ⟨(F.vanishing_event T hT).tMinus_nonnegative.trans ht.1, ht.2.le⟩

/-- Local finiteness gives finite included compact prefixes in Lemma 17.12, p. 410. -/
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

/-- Both included endpoints suffice for the finite-prefix use of Lemma 17.12, p. 410. -/
theorem surgeryTimes_inter_Icc_finite {a b : ℝ}
    (ha : a ∈ F.time_domain) (hb : b ∈ F.time_domain) :
    (F.surgery_times ∩ Icc a b).Finite :=
  surgeryTimes_inter_finite F isCompact_Icc (F.time_domain_interval.out ha hb)

/-- All earlier included slices are nonempty before a vanishing event
(MT Lemma 17.12, pp. 410-411). -/
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

/-- At most one surgery has an empty post-slice, as needed for MT Lemma 17.12, p. 411. -/
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

/-- Empty post-slices give the vanishing-volume clause of Lemma 17.12, pp. 410-411. -/
theorem vanishingVolumeData (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] : RepairedVanishingVolumeData F T hT where
  post_volume_zero := by rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty]
  volume_drop := by
    rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty]
    exact bot_le

end PoincareMT.SurgeryVolume
