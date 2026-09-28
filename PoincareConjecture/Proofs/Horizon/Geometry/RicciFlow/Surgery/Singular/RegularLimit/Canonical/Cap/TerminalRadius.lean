import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Radius










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem eventually_exists_cap_core_calibrated_radius
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t), N.connection = F.connection t →
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
      ∀ a b R : ℝ, 0 < a → a ≤ b → b < R →
      IsCompact (closure ((H.terminalMetric P04).ball x R)) →
      (H.terminalMetric P04).ball x a ⊆ H.regularReferencePreimage P04 t ht
        ((F.metric t).ball (H.reference.forward t ht x)
          (N.core_radius (H.reference.forward t ht x))) →
      H.regularReferencePreimage P04 t ht
        ((F.metric t).ball (H.reference.forward t ht x)
          (N.core_radius (H.reference.forward t ht x))) ⊆
        (H.terminalMetric P04).ball x b →
      (N.core_radius (H.reference.forward t ht x))⁻¹ ^ 2 + δ ≤ a⁻¹ ^ 2 →
      b⁻¹ ^ 2 ≤ (N.core_radius (H.reference.forward t ht x))⁻¹ ^ 2 - δ →
      ∃ r ∈ Icc a b,
        scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04)
          ((H.terminalMetric P04).ball x r) = r⁻¹ ^ 2 := by
  have hcont := (P04.tensor_calculus 3 (H.regularRegion P04) (H.terminalMetric P04)
    (H.terminalConnection P04)).contMDiff_scalarCurvature.continuous
  filter_upwards [H.eventually_cap_core_calibration_close P04 hA hδ] with t hcal
  intro ht N hconnection hcapture x hx a b R ha hab hbR hcompact hsmall hlarge hleft hright
  exact exists_scalar_calibrated_radius_of_sandwich
    (H.terminalMetric P04) (H.terminalConnection P04) hcont x ha hab hbR
    hcompact hsmall hlarge (hcal ht N hconnection hcapture _ hx).le hleft hright

end PoincareConjecture.SingularTimeAssumptions
