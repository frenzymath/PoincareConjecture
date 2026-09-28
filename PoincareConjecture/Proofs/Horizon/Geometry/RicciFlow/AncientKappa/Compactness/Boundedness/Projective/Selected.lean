import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.TerminalCloseness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.BlowupProduct








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance projectiveSelectedCarrierConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

namespace SelectedAncientRescalings

variable {b κ : ℝ} {F : RicciFlow 3 M (Iic b)} {p : M}
  (S : SelectedAncientRescalings F κ p)



theorem exists_terminal_projectiveNeck_threshold
    (P : M23NormalizedKappaCompactnessPredecessors)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
      ∀ B : RoundProductBlowup S δ,
      ∀ (Φ : RoundCylinderSpace → B.convergence.limitCarrier.carrier) (x : UnitTwoSphere),
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        Φ (x, 0) = B.convergence.base →
        (∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) →
        (fun z v w => (B.convergence.limitFlow.connection 0).scalarCurvature B.convergence.base *
          roundCylinderPullback (B.convergence.limitFlow.metric 0) Φ z v w) =
            EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop,
          IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
            (B.convergence.embedding i ∘ Φ) (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
          (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
            B.convergence.embedding i (Φ z) = B.convergence.embedding i (Φ w) ↔
              w = z ∨ w = (-z.1, z.2)) ∧
          B.convergence.embedding i (Φ (x, 0)) = S.center (B.convergence.subsequence i) ∧
          RoundCylinderClose ε 0 (fun z v w =>
            (F.connection b).scalarCurvature (S.center (B.convergence.subsequence i)) *
              roundCylinderPullback (F.metric b) (B.convergence.embedding i ∘ Φ) z v w) ∧
          ∃ e : RealProjectiveTwo ≃ₜ Set.range (fun q : UnitTwoSphere =>
              B.convergence.embedding i (Φ (q, 0))),
            ∀ q : UnitTwoSphere, (e (Quotient.mk realProjectiveTwoSetoid q)).val =
              B.convergence.embedding i (Φ (q, 0)) := by
  obtain ⟨η, hη, hterminal⟩ := RawAncientSequence.exists_terminal_projectiveNeck_threshold
    (fun _ => FlowCarrier.ofConnectedManifold 3 M) S.flow S.center P
    S.complete S.nonnegative
    (fun i => S.radius i * Real.sqrt ((F.connection b).scalarCurvature (S.center i)))
    S.radii_diverge S.curvature_bound S.normalized S.scalar_base_le hε
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδone hδη B Φ x hΦ hx hfiber hround
  filter_upwards [hterminal hδ hδone hδη B.convergence (B.complete 0 hδ)
    B.scalar_base_ge Φ x hΦ hx hfiber hround,
    B.convergence.eventually_projectiveCentralSection_homeomorph Φ hΦ hfiber]
    with i hneck htop
  refine ⟨hneck.1, hneck.2.1, hneck.2.2.1, ?_, htop⟩
  have hcl := hneck.2.2.2
  rw [S.terminal_metric_eq_rescaled] at hcl
  exact hcl




theorem exists_roundProductBlowup_with_terminal_projective_necks
    (P : M23NormalizedKappaCompactnessPredecessors) (hκ : 0 < κ)
    (hc : MetricComplete (F.metric b))
    (hop : ∀ x, (F.connection b).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ B : RoundProductBlowup S δ,
      ∀ (Φ : RoundCylinderSpace → B.convergence.limitCarrier.carrier) (x : UnitTwoSphere),
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        Φ (x, 0) = B.convergence.base →
        (∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) →
        (fun z v w => (B.convergence.limitFlow.connection 0).scalarCurvature B.convergence.base *
          roundCylinderPullback (B.convergence.limitFlow.metric 0) Φ z v w) =
            EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop,
          IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
            (B.convergence.embedding i ∘ Φ) (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
          (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
            B.convergence.embedding i (Φ z) = B.convergence.embedding i (Φ w) ↔
              w = z ∨ w = (-z.1, z.2)) ∧
          B.convergence.embedding i (Φ (x, 0)) = S.center (B.convergence.subsequence i) ∧
          RoundCylinderClose ε 0 (fun z v w =>
            (F.connection b).scalarCurvature (S.center (B.convergence.subsequence i)) *
              roundCylinderPullback (F.metric b) (B.convergence.embedding i ∘ Φ) z v w) ∧
          ∃ e : RealProjectiveTwo ≃ₜ Set.range (fun q : UnitTwoSphere =>
              B.convergence.embedding i (Φ (q, 0))),
            ∀ q : UnitTwoSphere, (e (Quotient.mk realProjectiveTwoSetoid q)).val =
              B.convergence.embedding i (Φ (q, 0)) := by
  obtain ⟨η, hη, hterminal⟩ := S.exists_terminal_projectiveNeck_threshold P hε
  obtain ⟨δ, hδ, hδone, hδη, ⟨B⟩⟩ := S.exists_roundProductBlowup P hκ hc hop hmono η hη
  exact ⟨δ, hδ, hδone, B, hterminal hδ hδone.le hδη B⟩

end SelectedAncientRescalings

end PoincareConjecture.RicciFlow
