import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.PositiveSectional










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)
  (hempty : I.controlled_core = ∅)

def vanishingEvent : SurgeryVanishingEventData F.parameters F.slice F.metric T := by
  let r := I.vanishingReferenceTime
  let s := Classical.choose (B.exists_rebase_canonical_tail hempty r)
  have hs := Classical.choose_spec (B.exists_rebase_canonical_tail hempty r)
  refine {
    tMinus := r.1
    tMinus_nonnegative := F.time_domain_nonnegative (I.last_slab.time_subset r.2)
    tMinus_lt := r.2.2
    pre_nonempty := I.last_slab.rebase_nonempty r
    pre_flow := I.last_slab.rebaseFlow r
    pre_identify := I.last_slab.rebaseIdentify r
    pre_initial := I.last_slab.rebaseIdentify_initial r
    pre_metric := I.last_slab.rebase_metric r
    left_limit_volume := Classical.choose I.exists_finite_left_volume
    left_limit_volume_tendsto := (Classical.choose_spec I.exists_finite_left_volume).2
    disappearing_start := s
    disappearing_start_bounds := ⟨hs.1, hs.2.1⟩
    disappearing_curvature := ?_
    disappearing_cover := ?_ }
  · intro a ha
    exact B.rebase_uniform_scalar_tail hempty r a (I.rho_eq ▸ ha)
  · intro t ht x
    let q : Ico r.1 T := ⟨t, hs.1.le.trans ht.1, ht.2⟩
    have he : MetricHomothety ((I.last_slab.rebaseFlow r).metric t) (F.metric t)
        (I.last_slab.rebaseIdentify r q) 1 := by
      intro y v w
      simpa only [one_mul] using I.last_slab.rebase_metric r q y v w
    have hcover := SurgeryCanonicalControl.pullback_static_cover (F.slice r.1)
      ((I.last_slab.rebaseFlow r).metric t) ((I.last_slab.rebaseFlow r).connection t)
      (I.last_slab.rebaseIdentify r q) he x
      (hs.2.2 t ht (I.last_slab.rebaseIdentify r q x))
    rcases hcover with hneck | hcap | hpositive | ⟨R, hx⟩
    · exact Or.inl hneck
    · exact Or.inr (Or.inl hcap)
    · exact Or.inr (Or.inr hpositive)
    · refine Or.inr (Or.inr ⟨R.carrier, hx, ?_, ?_⟩)
      · rw [R.component_eq] at hx ⊢
        exact connectedComponent_eq hx
      · exact R.positive_sectional ((I.last_slab.rebaseFlow r).connection t)
          F.parameters.epsilon_le

@[simp] theorem vanishingEvent_tMinus :
    (B.vanishingEvent hempty).tMinus =
      I.vanishingReference := rfl

theorem vanishingEvent_slab_compatibility :
    let V := B.vanishingEvent hempty
    ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
      ∀ hs' : s ∈ Ico V.tMinus T, ∀ ht' : t ∈ Ico V.tMinus T, ∀ x,
        (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
          (V.pre_identify ⟨s, hs'⟩ x) = V.pre_identify ⟨t, ht'⟩ x :=
  I.last_slab.rebase_transport I.vanishingReferenceTime

theorem vanishingEvent_terminalPolicy :
    SurgeryVanishingEventTerminalPolicy
      (B.vanishingEvent hempty) := by
  intro x
  have h := B.rebase_pointwise_strict_scalar_tail hempty I.vanishingReferenceTime x
  rw [I.rho_eq] at h
  exact h

theorem vanishingEvent_left_limit_volume_ne_top :
    (B.vanishingEvent hempty).left_limit_volume ≠ ⊤ :=
  (Classical.choose_spec I.exists_finite_left_volume).1

end PoincareConjecture.RepairedContinuationLimitBridge
