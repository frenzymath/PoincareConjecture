import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Capture

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit.RoundComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_late_roundComponent_terminal_carrier
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold) (x : H.regularRegion P04) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
        ∀ N : SingularRoundComponent (F.metric t) H.epsilon,
          H.reference.forward t ht x ∈ N.carrier →
          H.reference.inverse t ht '' N.carrier = connectedComponent (x : M) ∧
          connectedComponent (x : M) ⊆ H.reference.regularLimitSet ∧
          connectedComponent x = Subtype.val ⁻¹' connectedComponent (x : M) ∧
          IsCompact (connectedComponent x) := by
  obtain ⟨A, hA, hAreg, s, hsref, hsT, hcapture⟩ :=
    H.exists_compact_roundComponent_carrier_capture P04 hepsilon x.property
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht hst N hxN
  have hcarrier : H.reference.inverse t ht '' N.carrier = connectedComponent (x : M) := by
    have hcomponent := connectedComponent_eq (N.component_eq ▸ hxN)
    rw [N.component_eq, hcomponent]
    exact H.reference.inverse_image_connectedComponent t ht x
  have hreg : connectedComponent (x : M) ⊆ H.reference.regularLimitSet := by
    rw [← hcarrier]
    exact subset_closure.trans ((hcapture t ht hst N hxN).trans hAreg)
  have hterminal := SingularRegularLimit.connectedComponent_subtype_eq_preimage x hreg
  refine ⟨hcarrier, hreg, hterminal, ?_⟩
  rw [hterminal]
  apply Topology.IsInducing.subtypeVal.isCompact_preimage'
  · rw [← hcarrier]
    exact N.compact.image (H.reference.inverse_smooth t ht).continuous
  · rw [Subtype.range_coe]
    exact hreg

theorem frequently_regularRoundComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold) (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularRoundComponent (F.metric t) H.epsilon,
        H.reference.forward t ht x ∈ N.carrier) :
    ∃ᶠ t in 𝓝[<] T, ∃ N : SingularRoundComponent ((H.terminalFlow P04).metric t) H.epsilon,
      N.carrier = connectedComponent x ∧ x ∈ N.carrier := by
  obtain ⟨s, _, hsT, hcap⟩ := H.exists_late_roundComponent_terminal_carrier P04 hepsilon x
  have hsEv : ∀ᶠ t in 𝓝[<] T, s ≤ t :=
    (eventually_ge_nhds hsT).filter_mono nhdsWithin_le_nhds
  apply (hfreq.and_eventually hsEv).mono
  rintro t ⟨⟨ht, N, hxN⟩, hst⟩
  obtain ⟨_, hreg, hterminal, _⟩ := hcap t ht hst N hxN
  let N' := H.reference.referenceRoundComponent t ht N
  have hcarrier : N'.carrier = connectedComponent (x : M) :=
    H.reference.referenceRoundComponent_carrier t ht N hxN
  have hNU : N'.carrier ⊆ H.regularRegion P04 := by
    rw [hcarrier]
    exact hreg
  let NR := N'.restrictToOpen (H.regularRegion P04) hNU ((H.terminalFlow P04).metric t)
    (fun y v w => by
      rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
      exact (H.terminalMetricFamily_inner_of_ne P04 ht.2.ne y v w).symm)
  have hNR : NR.carrier = connectedComponent x := by
    change (Subtype.val : H.regularRegion P04 → M) ⁻¹' N'.carrier = connectedComponent x
    rw [hcarrier]
    exact hterminal.symm
  exact ⟨NR, hNR, hNR ▸ mem_connectedComponent⟩

theorem compact_component_of_frequently_roundComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold) (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularRoundComponent (F.metric t) H.epsilon,
        H.reference.forward t ht x ∈ N.carrier) : IsCompact (connectedComponent x) := by
  obtain ⟨t, N, hN, _⟩ := (H.frequently_regularRoundComponent P04 hepsilon x hfreq).exists
  exact hN ▸ N.compact

end PoincareConjecture.SingularTimeAssumptions
