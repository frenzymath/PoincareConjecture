import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Carrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Perturbation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Upgrade
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Accuracy



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



theorem exists_terminal_roundComponent_doubled_of_frequently
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold) (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularRoundComponent (F.metric t) H.epsilon,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ∃ N : SingularRoundComponent (H.terminalMetric P04) (2 * H.epsilon),
      N.carrier = connectedComponent x ∧ x ∈ N.carrier := by
  have hε := H.epsilon_pos
  have hcompact := H.compact_component_of_frequently_roundComponent P04 hepsilon x hfreq
  have hm : ⌊(2 * H.epsilon)⁻¹⌋₊ ≤ ⌊H.epsilon⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (by positivity) H.epsilon_pos).2 (by linarith [H.epsilon_pos]))
  have hpert := H.eventually_roundComponent_terminal_perturbation P04 hepsilon x hpos hcompact
    ⌊(2 * H.epsilon)⁻¹⌋₊ hm (show 0 < H.epsilon ^ 2 / 2 by positivity)
  obtain ⟨t, ⟨N, hcarrier, hx⟩, herr⟩ :=
    ((H.frequently_regularRoundComponent P04 hepsilon x hfreq).and_eventually hpert).exists
  let NT := N.changeMetric (H.terminalMetric P04) (herr N hx (hcarrier ▸ subset_rfl))
  exact ⟨NT, hcarrier, hx⟩


theorem exists_terminal_roundComponent_of_frequently
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold) (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularRoundComponent (F.metric t) H.epsilon,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ∃ N : SingularRoundComponent (H.terminalMetric P04)
        (terminalAccuracyFactor * H.epsilon),
      N.carrier = connectedComponent x ∧ x ∈ N.carrier := by
  obtain ⟨N, hcarrier, hx⟩ :=
    H.exists_terminal_roundComponent_doubled_of_frequently P04 hepsilon x hfreq hpos
  exact ⟨N.restrictAccuracy
    (mul_le_mul_of_nonneg_right two_le_terminalAccuracyFactor H.epsilon_pos.le), hcarrier, hx⟩

end PoincareConjecture.SingularTimeAssumptions
