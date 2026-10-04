import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Global.GlobalStageComparison

/-!
# Literal time-slice representatives of the completed-stage chain

Morgan--Tian Section 17.2, pp. 409-411, and global assembly contract steps
4-5. Choose the least strictly covering observation at nonnegative times,
retain the input's unused negative-time data, and identify every old slice
with that representative. Surgery times stabilize on every old raw domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : Nat}
  (Q : CompletedStageChain S N C F0 k)

/-- The least stage whose observation strictly contains the requested time.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def representativeIndex (t : Real) : Nat := by
  classical
  exact Nat.find (Q.exists_lt_horizon t)

/-- Strict coverage, including at dyadic boundary times.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem representative_horizon (t : Real) :
    t < (Q.observation (Q.representativeIndex t)).H := by
  classical
  exact Nat.find_spec (Q.exists_lt_horizon t)

/-- The selected stage contains each nonnegative time in its raw domain.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem representative_time (t : Real) (ht : 0 <= t) :
    t ∈ (Q.flow (Q.representativeIndex t)).time_domain :=
  Q.mem_time_domain_of_lt_horizon _ ht (Q.representative_horizon t)

/-- Total representative flow; negative-time data are the original input's.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def representativeFlow (t : Real) : SurgeryFlowData.{u} :=
  if 0 <= t then Q.flow (Q.representativeIndex t) else F0

/-- The global carrier is a literal selected carrier in the same universe.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def globalSlice (t : Real) : GeneralizedSliceCarrier.{u} :=
  (Q.representativeFlow t).slice t

/-- The global metric is the actual selected metric.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def globalMetric (t : Real) :
    RiemannianMetric 3 (Q.globalSlice t).carrier :=
  (Q.representativeFlow t).metric t

/-- Keep the selected connection representative on the selected metric.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def globalConnection (t : Real) : LeviCivitaData (Q.globalMetric t) :=
  (Q.representativeFlow t).connection t

/-- All old-slice maps at one time, with their metric and common-stage
identities. Keeping these together transports dependent carrier types once.
Morgan--Tian Section 17.2, pp. 409-411. -/
structure SliceIdentifications (t : Real) (G : SurgeryFlowData.{u}) where
  identify : ∀ n, t ∈ (Q.flow n).time_domain →
    Diffeomorph (𝓡 3) (𝓡 3) ((Q.flow n).slice t).carrier (G.slice t).carrier ∞
  metric : ∀ n ht x v w,
    (G.metric t).inner (identify n ht x)
      (mfderiv (𝓡 3) (𝓡 3) (identify n ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify n ht) x w) =
        ((Q.flow n).metric t).inner x v w
  compatible : ∀ n m (hnm : n <= m) ht x,
    identify m (Q.stageTime n m hnm ht) (Q.stageIdentify n m hnm t ht x) =
      identify n ht x

/-- Realize the entire compatible family on the literal selected flow.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def representativeMaps (t : Real) (ht0 : 0 <= t) :
    Q.SliceIdentifications t (Q.representativeFlow t) := by
  unfold representativeFlow
  rw [if_pos ht0]
  refine {
    identify := fun n ht => Q.compare n (Q.representativeIndex t) t ht
      (Q.representative_time t ht0)
    metric := fun n ht x v w => Q.compare_metric n (Q.representativeIndex t) t ht
      (Q.representative_time t ht0) x v w
    compatible := ?_ }
  intro n m hnm ht x
  simpa only [Q.compare_of_le n m hnm] using
    Q.compare_comp n m (Q.representativeIndex t) t ht (Q.stageTime n m hnm ht)
      (Q.representative_time t ht0) x

/-- Identify any stage's whole old slice with the global representative.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def globalIdentify (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) ((Q.flow n).slice t).carrier
      (Q.globalSlice t).carrier ∞ :=
  (Q.representativeMaps t ((Q.flow n).time_domain_nonnegative ht)).identify n ht

/-- The global representative map preserves the actual metric tensor.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalIdentify_metric (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) (x : ((Q.flow n).slice t).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (Q.globalMetric t).inner (Q.globalIdentify n t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (Q.globalIdentify n t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Q.globalIdentify n t ht) x w) =
        ((Q.flow n).metric t).inner x v w :=
  (Q.representativeMaps t ((Q.flow n).time_domain_nonnegative ht)).metric n ht x v w

/-- The representative map is a scale-one homothety for M13 calculus.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalIdentify_homothety (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) :
    MetricHomothety ((Q.flow n).metric t) (Q.globalMetric t)
      (Q.globalIdentify n t ht) 1 := by
  intro x v w
  simpa only [one_mul] using Q.globalIdentify_metric n t ht x v w

/-- Compatibility with every actual finite extension map.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalIdentify_comp (n m : Nat) (hnm : n <= m) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) (x : ((Q.flow n).slice t).carrier) :
    Q.globalIdentify m t (Q.stageTime n m hnm ht)
      (Q.stageIdentify n m hnm t ht x) = Q.globalIdentify n t ht x :=
  (Q.representativeMaps t ((Q.flow n).time_domain_nonnegative ht)).compatible n m hnm ht x

/-- The surgery set is the union of the actual completed-stage surgery sets.
Morgan--Tian Section 17.2, pp. 409-411. -/
def globalSurgeryTimes : Set Real := {t | ∃ n, t ∈ (Q.flow n).surgery_times}

/-- Every finite-stage surgery belongs to the global union.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem surgery_mem_global (n : Nat) {t : Real}
    (ht : t ∈ (Q.flow n).surgery_times) : t ∈ Q.globalSurgeryTimes := ⟨n, ht⟩

/-- The union agrees with every stage on that stage's whole raw domain.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem global_surgery_iff (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) :
    t ∈ Q.globalSurgeryTimes ↔ t ∈ (Q.flow n).surgery_times := by
  constructor
  · rintro ⟨m, hm⟩
    have hmq := ComposedExtension.oldSurgeryTimeTo
      (Q.extensionBetween m (max n m) (le_max_right _ _))
      (Q.extensionBetween_eq m (max n m) (le_max_right _ _))
      t ((Q.flow m).surgery_times_subset hm)
    have hnq := ComposedExtension.oldSurgeryTimeTo
      (Q.extensionBetween n (max n m) (le_max_left _ _))
      (Q.extensionBetween_eq n (max n m) (le_max_left _ _)) t ht
    exact hnq.mp (hmq.mpr hm)
  · exact Q.surgery_mem_global n

/-- All global surgery times are nonnegative.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalSurgeryTimes_nonnegative : Q.globalSurgeryTimes ⊆ Ici 0 := by
  rintro t ⟨n, hn⟩
  exact (Q.flow n).time_domain_nonnegative ((Q.flow n).surgery_times_subset hn)

/-- The union introduces no surgery at zero.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem zero_not_globalSurgeryTimes : 0 ∉ Q.globalSurgeryTimes := by
  rintro ⟨n, hn⟩
  exact (Q.flow n).zero_not_surgery hn

/-- Local finiteness is inherited within a strictly covering observation.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalSurgeryTimes_locally_finite (t : Real) (ht : 0 <= t) :
    ∃ d : Real, 0 < d ∧ (Q.globalSurgeryTimes ∩ Ioo (t - d) (t + d)).Finite := by
  obtain ⟨n, hn⟩ := Q.exists_lt_horizon (t + 1)
  have htF := Q.mem_time_domain_of_lt_horizon n ht (by linarith : t < (Q.observation n).H)
  obtain ⟨d, hd, hfinite⟩ := (Q.flow n).surgery_times_locally_finite t htF
  refine ⟨min 1 d, lt_min (by norm_num) hd, hfinite.subset ?_⟩
  intro s hs
  have he1 : min 1 d <= 1 := min_le_left _ _
  have hed : min 1 d <= d := min_le_right _ _
  have hsF := Q.mem_time_domain_of_lt_horizon n
    (Q.globalSurgeryTimes_nonnegative hs.1)
    (by linarith [hs.2.2] : s < (Q.observation n).H)
  exact ⟨(Q.global_surgery_iff n s hsF).mp hs.1,
    ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩⟩

end PoincareMT.M51.CompletedStageChain
