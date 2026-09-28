import PoincareConjecture.Definitions.M33RegularHistory

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem SurgeryFlowData.surgery_times_finite_on_compact
    (F : SurgeryFlowData.{u}) {K : Set ℝ} (hK : IsCompact K)
    (hKF : K ⊆ F.time_domain) : (F.surgery_times ∩ K).Finite := by
  classical
  choose d hd hfinite using
    (fun t : K => F.surgery_times_locally_finite t.1 (hKF t.2))
  let U (t : K) : Set ℝ := Set.Ioo (t.1 - d t) (t.1 + d t)
  obtain ⟨cover, hcover⟩ := hK.elim_finite_subcover U
    (fun _ => isOpen_Ioo) (by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, by
        change t - d ⟨t, ht⟩ < t ∧ t < t + d ⟨t, ht⟩
        constructor <;> linarith [hd ⟨t, ht⟩]⟩)
  apply (cover.finite_toSet.biUnion (fun t _ => hfinite t)).subset
  intro t ht
  obtain ⟨s, hs, htU⟩ := Set.mem_iUnion₂.mp (hcover ht.2)
  exact Set.mem_iUnion₂.mpr ⟨s, hs, ht.1, htU⟩

theorem RepairedPreterminalSlab.initial_interval_subset
    {F : SurgeryFlowData.{u}} {T : ℝ} (P : RepairedPreterminalSlab F T) :
    Set.Ico 0 T ⊆ F.time_domain := by
  intro t ht
  by_cases h : t ≤ P.start
  · exact F.time_domain_interval.out F.zero_mem P.start_mem ⟨ht.1, h⟩
  · exact P.time_subset ⟨(lt_of_not_ge h).le, ht.2⟩

theorem RepairedPreterminalSlab.initial_slices_nonempty
    {F : SurgeryFlowData.{u}} {T : ℝ} (P : RepairedPreterminalSlab F T) :
    ∀ t ∈ Set.Ico 0 T, Nonempty (F.slice t).carrier := by
  obtain ⟨s, _, x, _⟩ := P.curvature_unbounded 0 P.start P.start_lt
  intro t ht
  by_cases h : P.start ≤ t
  · exact ⟨P.identify ⟨t, h, ht.2⟩ x⟩
  · by_contra hne
    exact (F.extinction_permanent t P.start (P.initial_interval_subset ht)
      P.start_mem (lt_of_not_ge h).le ⟨fun y => hne ⟨y⟩⟩).false x

theorem RepairedPreterminalSlab.initial_events_finite
    {F : SurgeryFlowData.{u}} {T : ℝ} (P : RepairedPreterminalSlab F T) :
    (F.surgery_times ∩ Set.Ico 0 T).Finite := by
  have hprefix : Set.Icc 0 P.start ⊆ F.time_domain :=
    F.time_domain_interval.out F.zero_mem P.start_mem
  apply (F.surgery_times_finite_on_compact isCompact_Icc hprefix).subset
  intro t ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  by_contra h
  exact Set.disjoint_left.mp P.surgery_free ht.1 ⟨lt_of_not_ge h, ht.2.2⟩

def RepairedPreterminalSlab.regularHistoryWindow
    {F : SurgeryFlowData.{u}} {T : ℝ} (P : RepairedPreterminalSlab F T) :
    M33RegularHistoryWindow F where
  interval := Set.Ico 0 T
  interval_connected := Set.ordConnected_Ico
  interval_nontrivial := by
    have hT : 0 < T := lt_of_le_of_lt
      (F.time_domain_nonnegative P.start_mem) P.start_lt
    refine ⟨0, ⟨le_rfl, hT⟩, T / 2, ⟨by linarith, by linarith⟩, ?_⟩
    linarith
  zero_mem := ⟨le_rfl, lt_of_le_of_lt
    (F.time_domain_nonnegative P.start_mem) P.start_lt⟩
  time_subset := P.initial_interval_subset
  slice_nonempty := P.initial_slices_nonempty
  events_finite := P.initial_events_finite

def SurgeryFlowData.closedRegularHistoryWindow (F : SurgeryFlowData.{u})
    (H : ℝ) (hH : 0 < H) (hHmem : H ∈ F.time_domain)
    (hne : Nonempty (F.slice H).carrier) : M33RegularHistoryWindow F where
  interval := Set.Icc 0 H
  interval_connected := Set.ordConnected_Icc
  interval_nontrivial := ⟨0, ⟨le_rfl, hH.le⟩, H, ⟨hH.le, le_rfl⟩, hH.ne⟩
  zero_mem := ⟨le_rfl, hH.le⟩
  time_subset := F.time_domain_interval.out F.zero_mem hHmem
  slice_nonempty := by
    intro t ht
    by_contra hempty
    obtain ⟨x⟩ := hne
    exact (F.extinction_permanent t H
      (F.time_domain_interval.out F.zero_mem hHmem ht) hHmem ht.2
      ⟨fun y => hempty ⟨y⟩⟩).false x
  events_finite := F.surgery_times_finite_on_compact isCompact_Icc
    (F.time_domain_interval.out F.zero_mem hHmem)

theorem m33RegularRegion_of_regular (F : SurgeryFlowData.{u}) (t : ℝ)
    (ht : t ∉ F.surgery_times) : m33RegularRegion F t = Set.univ := by
  ext x
  simp [m33RegularRegion, ht]

theorem m33RegularRegion_of_surgery (F : SurgeryFlowData.{u}) (t : ℝ)
    (ht : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier] :
    m33RegularRegion F t = interior (F.event t ht).retained_post := by
  ext x
  exact ⟨fun h => h ht, fun h _ => h⟩

end PoincareConjecture
