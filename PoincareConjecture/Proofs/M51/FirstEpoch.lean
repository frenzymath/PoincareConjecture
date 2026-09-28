import PoincareConjecture.Proofs.M51.NormalizedStart
import PoincareConjecture.Proofs.M51.EpochControls

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51Initial

theorem firstObservation (F : SurgeryFlowData.{u})
    (standard_flow : MaximalStandardCapFlow F.standard_initial)
    (hshape : F.time_domain = Ici 0 ∨
      ∃ T : ℝ, 1 / 16 < T ∧ F.time_domain = Ico 0 T ∧
        ∃ L : RepairedPreterminalSlab F T, L.start = 0) :
    ∃ O : SurgeryObservation F,
      1 / 16 < O.H ∧ O.H ≤ 1 / 8 ∧ O.standard_flow = standard_flow ∧
      (O.H < 1 / 8 → F.time_domain = Ico 0 O.H ∧
        ∃ L : RepairedPreterminalSlab F O.H, L.start = 0) ∧
      (F.time_domain = Ico 0 O.H →
        ∃ L : RepairedPreterminalSlab F O.H, L.start = 0) := by
  rcases hshape with hJ | ⟨T, hT, hJ, L, hL⟩
  · let O : SurgeryObservation F := {
      H := 1 / 8
      H_pos := by norm_num
      interval_subset := by rw [hJ]; exact fun _ ht => ht.1
      standard_flow := standard_flow }
    refine ⟨O, by norm_num [O], le_rfl, rfl, ?_, ?_⟩
    · intro hlt
      exact (lt_irrefl _ hlt).elim
    · intro h
      have ht : O.H ∈ F.time_domain := hJ ▸ (show 0 ≤ O.H by norm_num [O])
      rw [h] at ht
      exact (lt_irrefl _ ht.2).elim
  · let O : SurgeryObservation F := {
      H := min T (1 / 8)
      H_pos := lt_min (lt_trans (by norm_num) hT) (by norm_num)
      interval_subset := by
        intro t ht
        rw [hJ]
        exact ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
      standard_flow := standard_flow }
    have hslab (h : F.time_domain = Ico 0 O.H) :
        ∃ next : RepairedPreterminalSlab F O.H, next.start = 0 := by
      have hTeq : T = O.H := by
        refine le_antisymm ?_ (min_le_left _ _)
        by_contra hn
        have ht : O.H ∈ F.time_domain :=
          hJ ▸ ⟨O.H_pos.le, lt_of_not_ge hn⟩
        rw [h] at ht
        exact lt_irrefl _ ht.2
      exact (congrArg (fun U : ℝ => ∃ next : RepairedPreterminalSlab F U,
        next.start = 0) hTeq).mp ⟨L, hL⟩
    refine ⟨O, lt_min hT (by norm_num), min_le_right _ _, rfl, ?_, hslab⟩
    intro hlt
    have hTH : T < (1 / 8 : ℝ) :=
      (min_lt_iff.mp hlt).resolve_right (lt_irrefl _)
    have hdomain : F.time_domain = Ico 0 O.H := by
      change F.time_domain = Ico 0 (min T (1 / 8))
      rw [min_eq_left hTH.le]
      exact hJ
    exact ⟨hdomain, hslab hdomain⟩

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]

theorem exists_first_epoch (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)
    (I : NormalizedInitialMetric (M := M))
    (hRP : NoTrivialNormalProjectivePlane (M := M))
    (delta : ℝ → ℝ) (hmono : AntitoneOn delta (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < delta t)
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∃ F : SurgeryFlowData.{u},
      F.standard_initial = S.setup.standard_initial ∧
      F.local_constants = S.constants ∧
      F.parameters = (M51Numerical.schedule S N C).parameters delta hmono hpos ∧
      F.slice = (fun _ => carrier M) ∧ F.surgery_times = ∅ ∧
      SurgeryFlowAdmissible F ∧ SurgeryFlowPinched F ∧
      (F.time_domain = Ici 0 ∨ ∃ T : ℝ, 1 / 16 < T ∧ F.time_domain = Ico 0 T ∧
        ∃ L : RepairedPreterminalSlab F T, L.start = 0) ∧
      (∃ e : Diffeomorph (𝓡 3) (𝓡 3) M (F.slice 0).carrier ∞,
        ∀ x v w, (F.metric 0).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
            I.metric.inner x v w) ∧
      ∃ O : SurgeryObservation F, 1 / 16 < O.H ∧ O.H ≤ 1 / 8 ∧
        HEq O.standard_flow S.setup.standard_flow ∧
        SurgeryPrefixControls (M51Numerical.prefixAt S N C 0) F O ∧
        SurgeryEpochContinuationControls (M51Numerical.prefixAt S N C 0) F O
          (M51Numerical.noncollapse S N C 0) (M51Numerical.canonical S N C 0) ∧
        SurgeryNoncollapsedOn F (surgeryObservationInterval O)
          (M51Numerical.noncollapse S N C 0).kappaNew ∧
        (O.H < 1 / 8 → F.time_domain = Ico 0 O.H ∧
          ∃ L : RepairedPreterminalSlab F O.H, L.start = 0) ∧
        (F.time_domain = Ico 0 O.H →
          ∃ L : RepairedPreterminalSlab F O.H, L.start = 0) := by
  obtain ⟨F, hstd, hK, hP, hslice, hS, hAd, hPin, hshape, hinit,
      O0, hH0, hStd0, hOld⟩ := exists_initial_flow S N C I hRP delta hmono hpos hcut
  obtain ⟨O, hstart, hend, hStd, hfront, hslab⟩ :=
    firstObservation F O0.standard_flow hshape
  have hprefix : SurgeryPrefixControls (M51Numerical.prefixAt S N C 0) F O :=
    hOld.observePastPrefix O (by norm_num [surgeryEpochStart, hH0]) hPin
  have hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t := by
    intro t _
    rw [hP]
    rfl
  have hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t) := by
    intro j t ht _
    rw [hP]
    exact ⟨GlobalSurgerySchedule.parameters_r _ _ _ _ ht,
      GlobalSurgerySchedule.parameters_kappa _ _ _ _ ht, rfl⟩
  have policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) := by
    constructor
    · intro t _ht hs
      exact (Set.notMem_empty t (hS ▸ hs)).elim
    · intro t _ht hs
      exact (Set.notMem_empty t (hS ▸ hs)).elim
  obtain ⟨hcontrols, hnoncollapsed⟩ := M51Numerical.continuationControls S N C
    0 F O delta hdelta hprofiles hcut hprefix hPin policy
    (by norm_num [M51Numerical.prefix_index, surgeryEpochStart]; linarith only [hstart])
    (by norm_num [M51Numerical.prefix_index, surgeryEpochStart]; linarith only [hend])
  exact ⟨F, hstd, hK, hP, hslice, hS, hAd, hPin, hshape, hinit,
    O, hstart, hend, hStd.heq.trans hStd0, hprefix, hcontrols, hnoncollapsed, hfront, hslab⟩

end PoincareConjecture.M51Initial
