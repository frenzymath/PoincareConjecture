import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.Twisted
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Unlift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ProjectivePlane

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

theorem exists_noncompact_lifted_limit_without_models
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ kappa : ℝ, 0 < kappa → ∀ C₀ : ℝ, 0 < C₀ →
          ∃ C : ℝ, 0 < C ∧
            ∀ S : NormalizedKappaSolutionSequence kappa,
              (∀ k, NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow) →
              Tendsto (fun k => metricDiameter ((S.term k).flow.flow.metric 0) univ)
                atTop atTop →
              (∀ k, ¬ ∃ N : StrongEvolvingNeck (S.term k).flow 0 epsilon,
                N.center = (S.term k).base) →
              (∀ k, ¬ ∃ A : CapCertificate ((S.term k).flow.flow.metric 0),
                A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ (S.term k).base ∈ A.core) →
              ∃ G : M23InteriorConvergence S,
                M23TerminalExtension G ∧
                let L : AncientKappaSolution 3 (ULift.{u} G.limit.carrier.carrier) :=
                  G.limit.flow.ulift
                ¬ IsCompact (univ : Set (ULift.{u} G.limit.carrier.carrier)) ∧
                NoEmbeddedTrivialNormalProjectivePlane L ∧
                (¬ ∃ N : StrongEvolvingNeck L 0 epsilon,
                  N.center = ULift.up G.limit.base) ∧
                (¬ ∃ A : CapCertificate (L.flow.metric 0),
                  A.epsilon = epsilon ∧ A.cap_constant ≤ C₀ ∧
                    ULift.up G.limit.base ∈ A.core) ∧
                ¬ Nonempty (M27SphereLineFlowCertificate L) ∧
                ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate L) ∧
                ¬ Nonempty (M27TwistedSphereLineFlowCertificate L) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hlimit⟩ :=
    exists_noncompact_limit_without_neighborhoods P
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro epsilon hepsilon hε kappa hkappa C₀ hC₀
  let B := max C₀ (twistedCapConstant P epsilon)
  have hB : 0 < B := hC₀.trans_le (le_max_left _ _)
  obtain ⟨C, hC, hlimit⟩ := hlimit kappa hkappa B hB
  refine ⟨C, hC, ?_⟩
  intro S hno hdiam hneck hcap
  obtain ⟨G, T, hnoncompact, hprojective, hnoneck, hnocap⟩ :=
    hlimit epsilon hepsilon hε S hno hdiam hneck hcap
  let L : AncientKappaSolution 3 (ULift.{u} G.limit.carrier.carrier) := G.limit.flow.ulift
  have hprojectiveL : NoEmbeddedTrivialNormalProjectivePlane L :=
    G.limit.flow.noEmbeddedTrivialNormalProjectivePlane_ulift hprojective
  have hnoneckL : ¬ ∃ N : StrongEvolvingNeck L 0 epsilon,
      N.center = ULift.up G.limit.base := by
    rintro ⟨N, hN⟩
    exact hnoneck ⟨G.limit.flow.strongNeckFromUlift N, by simp [hN]⟩
  have hnocapL : ¬ ∃ A : CapCertificate (L.flow.metric 0),
      A.epsilon = epsilon ∧ A.cap_constant ≤ B ∧ ULift.up G.limit.base ∈ A.core := by
    rintro ⟨A, hA, hAB, hx⟩
    exact hnocap ⟨G.limit.flow.flow.capFromUlift 0 A, hA, hAB, hx⟩
  refine ⟨G, T, ?_, hprojectiveL, hnoneckL, ?_, ?_,
    hprojectiveL.not_projectivePlaneLine, ?_⟩
  · intro hcompact
    apply hnoncompact
    simpa only [image_univ, EquivLike.range_eq_univ] using
      hcompact.image (Homeomorph.ulift : ULift.{u} G.limit.carrier.carrier ≃ₜ
        G.limit.carrier.carrier).continuous
  · rintro ⟨A, hA, hAC, hx⟩
    exact hnocapL ⟨A, hA, hAC.trans (le_max_left _ _), hx⟩
  · rintro ⟨model⟩
    exact hnoneckL (model.exists_strongEvolvingNeck le_rfl hepsilon
      ((hε.trans hsmall).trans_lt (by norm_num)) (ULift.up G.limit.base))
  · rintro ⟨model⟩
    obtain ⟨A, hA, hAC, _, hcover⟩ := model.exists_cap_core_or_strong_neck P
      le_rfl hepsilon ((hε.trans hsmall).trans (by norm_num))
    rcases hcover (ULift.up G.limit.base) with hx | hN
    · exact hnocapL ⟨A, hA, hAC ▸ le_max_right _ _, hx⟩
    · exact hnoneckL hN

end PoincareConjecture
