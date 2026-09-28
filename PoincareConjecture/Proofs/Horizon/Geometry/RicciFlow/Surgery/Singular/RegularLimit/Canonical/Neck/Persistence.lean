import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TailCloseness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Accuracy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

theorem exists_terminal_strong_neck_persistence_doubled_threshold
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ (hΩ : H.reference.regularLimitSet.Nonempty) (x : H.regularRegion P04),
          0 < (H.terminalConnection P04).scalarCurvature x →
          (∀ s : ℝ, s < T → ∃ t : ℝ, ∃ ht : t ∈ Ioo H.reference.tMinus T,
            s < t ∧ ∃ N : GeneralizedStrongNeck F t H.epsilon,
              N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x) →
          ∃ N : GeneralizedStrongNeck (H.nonemptyExtension P04 hΩ).extended T (2 * H.epsilon),
            N.center = (H.terminalSliceHomeomorph P04).symm x := by
  obtain ⟨εC, hεC, hsmallC, hcapture⟩ := exists_neck_cap_compact_capture_threshold.{u}
  obtain ⟨εS, hεS, _, hscalar⟩ := exists_neck_terminal_scalar_monotonicity_threshold P04
  refine ⟨min εC εS, lt_min hεC hεS, (min_le_left _ _).trans hsmallC, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε hΩ x hQ hnecks
  have hεC' : H.epsilon ≤ εC := hε.trans (min_le_left _ _)
  have hεS' : H.epsilon ≤ εS := hε.trans (min_le_right _ _)
  obtain ⟨A, hA, hAreg, sA, hsA, hsAT, hcapture⟩ := hcapture H P04 hεC' x x.property
  let AΩ : Set (H.regularRegion P04) := Subtype.val ⁻¹' A
  have hAΩ : IsCompact AΩ := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hA
    intro y hy
    exact ⟨⟨y, hAreg hy⟩, rfl⟩
  obtain ⟨sJ, hsJ, hsJT, hcomparison⟩ := H.exists_late_neck_terminal_metric_comparison
    P04 hΩ (hεC'.trans hsmallC) x hQ hAΩ
  obtain ⟨_, sS, hsS, hsST, hmono⟩ := hscalar H hεS' x hQ hnecks
  obtain ⟨t, ht, hlate, N, hcenter⟩ :=
    hnecks (max sA (max sJ sS)) (max_lt hsAT (max_lt hsJT hsST))
  have hsAt : sA < t := (le_max_left _ _).trans_lt hlate
  have hsJt : sJ < t := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hlate)
  have hsSt : sS < t := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hlate)
  have hlabels := (hcapture t ⟨ht.1.le, ht.2⟩ hsAt.le).1 N hcenter
  have hNA : H.reference.inverse t ⟨ht.1.le, ht.2⟩ '' N.carrier ⊆ Subtype.val '' AΩ := by
    intro y hy
    have hyA := hlabels (subset_closure hy)
    exact ⟨⟨y, hAreg hyA⟩, hyA, rfl⟩
  have hcaptureN : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      N.carrier H.reference.regularLimitSet :=
    fun _ hy => hAreg (hlabels (subset_closure (mem_image_of_mem _ hy)))
  have hR : (F.connection t).scalarCurvature N.center <
      (H.terminalConnection P04).scalarCurvature x := by
    have heq : (F.connection t).scalarCurvature N.center =
        ((H.terminalFlow P04).connection t).scalarCurvature x := by
      rw [H.terminalFlow_scalar_of_ne P04 ht.2.ne, hcenter]
      exact H.reference.scalar_pullback t ⟨ht.1.le, ht.2⟩ x
    rw [heq, ← H.terminalFlow_scalar_at_terminal P04 x]
    exact hmono ⟨hsSt, ht.2.le⟩ ⟨hsST, le_rfl⟩ ht.2
  have hclose := hcomparison t ht hsJt N hcenter hNA hR
  exact ⟨H.terminalStrongNeckOfComparison P04 hΩ ht N x hcenter hR
      (show H.epsilon ≤ 2 * H.epsilon by linarith [H.epsilon_pos]) hcaptureN hclose,
    H.terminalStrongNeckOfComparison_center P04 hΩ ht N x hcenter hR _ hcaptureN hclose⟩

theorem exists_terminal_strong_neck_persistence_threshold
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ (hΩ : H.reference.regularLimitSet.Nonempty) (x : H.regularRegion P04),
          0 < (H.terminalConnection P04).scalarCurvature x →
          (∀ s : ℝ, s < T → ∃ t : ℝ, ∃ ht : t ∈ Ioo H.reference.tMinus T,
            s < t ∧ ∃ N : GeneralizedStrongNeck F t H.epsilon,
              N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x) →
          ∃ N : GeneralizedStrongNeck (H.nonemptyExtension P04 hΩ).extended T
              (terminalAccuracyFactor * H.epsilon),
            N.center = (H.terminalSliceHomeomorph P04).symm x := by
  obtain ⟨ε₀, hε₀, hsmall, hneck⟩ :=
    exists_terminal_strong_neck_persistence_doubled_threshold P04
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε hΩ x hpos hnecks
  obtain ⟨N, hcenter⟩ := hneck H hε hΩ x hpos hnecks
  exact ⟨N.restrictAccuracy
    (mul_le_mul_of_nonneg_right two_le_terminalAccuracyFactor H.epsilon_pos.le), hcenter⟩

end PoincareConjecture.SingularRegularLimit
