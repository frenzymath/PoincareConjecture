import PoincareConjecture.Proofs.M51.InitialPresentation
import PoincareConjecture.Proofs.M51.InitialPinching
import PoincareConjecture.Proofs.M51.InitialControls
import PoincareConjecture.Proofs.M51.MaximalOrdinary
import PoincareConjecture.Proofs.M03

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51Initial

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]

theorem exists_initial_flow (S : RepairedControlledSchedulesData.{u})
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
      ∃ O : SurgeryObservation F, O.H = 1 / 16 ∧
        HEq O.standard_flow S.setup.standard_flow ∧
        SurgeryPrefixControls S.initialPrefix F O := by
  obtain ⟨J, G, hleast, h0, hshape⟩ :=
    M51Ordinary.exists_maximal_initial_flow (ricciFlowLocalTheory (n := 3) (M := M))
      I.metric
  let P := (M51Numerical.schedule S N C).parameters delta hmono hpos
  have hmax := maximality G hshape
  let F := rawFlow S.setup.standard_initial S.constants P I hRP G h0 hleast hmax
  have hAd : SurgeryFlowAdmissible F := admissible_of_no_events F rfl
  have hPin : SurgeryFlowPinched F := by
    apply pinched_on I G h0
    rcases hshape with hJ | ⟨T, hT, hJ, _⟩
    · exact Or.inl hJ
    · exact Or.inr ⟨T, hT, hJ⟩
  have hInitial : Icc 0 (1 / 16 : ℝ) ⊆ F.time_domain := by
    rcases hshape with hJ | ⟨T, hT, hJ, _⟩
    · intro t ht
      change t ∈ J
      exact hJ ▸ ht.1
    · have hTlarge := S.initialFrontier_lt F T hT hJ
      intro t ht
      change t ∈ J
      exact hJ ▸ ⟨ht.1, ht.2.trans_lt hTlarge⟩
  let O : SurgeryObservation F := {
    H := 1 / 16
    H_pos := by norm_num
    interval_subset := Ico_subset_Icc_self.trans hInitial
    standard_flow := S.setup.standard_flow }
  refine ⟨F, rfl, rfl, rfl, rfl, rfl, hAd, hPin, ?_, ?_, O, rfl, HEq.rfl, ?_⟩
  · rcases hshape with hJ | ⟨T, hT, hJ, _⟩
    · exact Or.inl hJ
    · exact Or.inr ⟨T, S.initialFrontier_lt F T hT hJ, hJ,
        preterminal S.setup.standard_initial S.constants P I hRP G h0 hleast hmax T hT hJ,
        rfl⟩
  · refine ⟨Diffeomorph.refl (𝓡 3) M ∞, ?_⟩
    intro x v w
    change (G.metric 0).inner (id x)
      (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x w) = _
    simp only [mfderiv_id, ContinuousLinearMap.id_apply, h0, id_eq]
  · exact prefix_controls S N C delta hmono hpos hcut F rfl rfl rfl hAd hPin O rfl

end PoincareConjecture.M51Initial
