import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.FamilyClose
import PoincareConjecture.Proofs.M32.Claim11_35.NeckTransfer.Eventual
import PoincareConjecture.Proofs.M32.Claim11_32.HornBalls












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}





theorem terminalBlowupConvergence_eventually_strongNecks_in_horns
    (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
    (Q : ∀ k, SingularLimitConclusion (H k))
    (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
    (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
    (hdiv : Tendsto (fun k =>
      ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
    {J : Set ℝ} (G : GeneralizedBlowupConvergence
      (terminalBlowupSequence H Q x hpos hdiv) J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (Phi : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    (q : UnitTwoSphere) (hcenter : Phi (q, 0) = G.limit.base)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmodel : ∀ s ∈ Icc (-1 : ℝ) 0,
      roundCylinderPullback (G.limit.flow.metric s) Phi = EvolvingRoundCylinderMetric s)
    (hM04 : RicciFlowCurvatureTheory.{u}) {K B : ℝ} {accuracy : ℕ → ℝ}
    (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension (accuracy k))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) :
    ∀ᶠ k : ℕ in atTop,
      ∃ N : GeneralizedStrongNeck (Q (G.subsequence k)).extension.extended
          (T (G.subsequence k)) delta,
        N.center = x (G.subsequence k) ∧ N.carrier ⊆ (horn (G.subsequence k)).carrier := by
  have hclose := blowup_eventually_roundCylinderFamilyClose G hJI Phi
    Phi.contMDiff hdelta hmodel
  obtain ⟨A, hA, hnecks⟩ :=
    blowup_eventually_strongNecks_of_cylinderFamilyClose G hJI Phi q hcenter hdelta hclose
  have hinside := G.subsequence_strictMono.tendsto_atTop.eventually
    (terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv hM04
      hK hB hcutoff hconstant horn hx hboundary A hA)
  filter_upwards [hnecks, hinside] with k hk hin
  obtain ⟨_hI, N, hNcenter, _hNscale, _hNcarrier, _hNcoordinate,
    _hNinverse, _hNsphere, _hNpoint, hNball⟩ := hk
  exact ⟨N, hNcenter, hNball.trans hin⟩

end PoincareConjecture.M32
