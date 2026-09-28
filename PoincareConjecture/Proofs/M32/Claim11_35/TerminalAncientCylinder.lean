import PoincareConjecture.Proofs.M32.Claim11_35.AncientCylinder
import PoincareConjecture.Proofs.M32.Claim11_35.AncientRoundFactor
import PoincareConjecture.Proofs.M32.Claim11_34.ProjectiveExclusion

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}

theorem terminalLongBlowupConclusion_exists_normalized_evolvingCylinder
    (P : RepairedHornSelectionPredecessors.{u})
    (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
    (Q : ∀ k, SingularLimitConclusion (H k))
    (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
    (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
    (hdiv : Tendsto (fun k =>
      ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
    {κ r₀ : ℝ}
    (G : RepairedLongControlledBlowupConclusion
      (terminalBlowupSequence H Q x hpos hdiv) κ r₀ ⊤)
    {K B : ℝ} {accuracy : ℕ → ℝ} (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension (accuracy k))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K)
    {Bcurv : ℝ} (hBcurv : 0 ≤ Bcurv)
    (hbound : ∀ t ≤ 0, ∀ y,
      (G.convergence.limit.flow.connection t).curvatureTensorNorm y ≤ Bcurv)
    (γ : ℝ → G.convergence.limit.carrier.carrier)
    (hγ : ∀ s t : ℝ,
      (G.convergence.limit.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
        G.convergence.limit.carrier.carrier) (q : UnitTwoSphere),
      Φ (q, 0) = G.convergence.limit.base ∧
        ∀ t ≤ 0, roundCylinderPullback (G.convergence.limit.flow.metric t) Φ =
          EvolvingRoundCylinderMetric t := by
  obtain ⟨C, hC⟩ := longBlowupConclusion_exists_compact_round_surface_product
    P G hBcurv hbound γ hγ
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  obtain ⟨A, _, ⟨hround⟩, e, hmetric, _⟩ := hC
  let : CompactSpace C.carrier := hround.compact
  have hno := terminalBlowupConvergence_no_projective_product H Q x hpos hdiv
    P.m04 hK hB hcutoff hconstant horn hx hboundary G.convergence
  exact roundProduct_exists_normalized_evolvingCylinder P.m04 A.flow
    hround.round_at_all_times G.convergence.limit.flow.metric
    (G.convergence.limit.flow.connection 0) e hmetric G.convergence.limit.base
    G.convergence.limit.scalar_normalized hno

end PoincareConjecture.M32
