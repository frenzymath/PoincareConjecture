import PoincareConjecture.Proofs.M51.FiniteEpoch









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51

open M51Numerical



theorem EpochStage.complete
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S} {C : RepairedCanonicalInductionData S N}
    {n : ℕ} {F : SurgeryFlowData.{u}} (X : EpochStage S N C n F)
    (calibration : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (d : ℝ) (hd : (schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial → G.local_constants = S.constants →
        O.H ≤ B → RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O → A.card ≤ bound)
    (delta : ℝ → ℝ)
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j) :
    ∃ Y : EpochStage S N C n F,
      Y.observation.H = surgeryEpochStart ((prefixAt S N C n).i + 1) := by
  obtain ⟨bound, hbound⟩ := uniformEpochEventCount S N C n F P.m13
    d hd count delta hdelta hcut
  exact X.reachBoundary calibration P delta hdelta hprofiles hcut bound hbound

end PoincareConjecture.M51

namespace PoincareConjecture.M51Initial

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]



theorem exists_first_stage (S : RepairedControlledSchedulesData.{u})
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
      (∃ e : Diffeomorph (𝓡 3) (𝓡 3) M (F.slice 0).carrier ∞,
        ∀ x v w, (F.metric 0).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
            I.metric.inner x v w) ∧
      ∃ X : M51.EpochStage S N C 0 F, X.extension = SurgeryFlowExtension.refl F := by
  obtain ⟨F, hstd, hK, hP, _hslice, hS, _hAd, hPin, hshape, hinit,
      O, hstart, hend, _hStd, hprefix, _hcontrols, _hnoncollapsed, hfront, _hslab⟩ :=
    exists_first_epoch S N C I hRP delta hmono hpos hcut
  have policy : SurgeryFlowTerminalPolicyOn F F.time_domain := by
    constructor
    · intro t _ht hs
      exact (Set.notMem_empty t (hS ▸ hs)).elim
    · intro t _ht hs
      exact (Set.notMem_empty t (hS ▸ hs)).elim
  have htail : M51.MaximalTail F := by
    rcases hshape with hglobal | ⟨T, hT, hJ, L, _hL⟩
    · exact Or.inl hglobal
    · exact Or.inr ⟨T, (by linarith only [hT]), hJ, ⟨L⟩⟩
  have hleft : surgeryEpochStart (M51Numerical.prefixAt S N C 0).i ≤ O.H := by
    norm_num [M51Numerical.prefix_index, surgeryEpochStart]
    exact hstart.le
  have hright : O.H ≤ surgeryEpochStart ((M51Numerical.prefixAt S N C 0).i + 1) := by
    norm_num [M51Numerical.prefix_index, surgeryEpochStart]
    exact hend
  refine ⟨F, hstd, hK, hP, hinit,
    M51.EpochStage.ofObservation O hprefix hPin policy htail hleft hright ?_, rfl⟩
  intro h
  apply (hfront ?_).1
  norm_num [M51Numerical.prefix_index, surgeryEpochStart] at h
  exact h

end PoincareConjecture.M51Initial
