import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.CollarSequence
import PoincareConjecture.Statements.M27Providers











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space

open CompactKappa



theorem exists_smallBased_without_neighborhoods_strong_collars_of_m27
    (P : M27KappaAlternativePredecessors.{u})
    {kappa epsilon C : ℝ} (hkappa : 0 < kappa)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) (p : M)
    (hnc : AncientKappaNoncollapsed K.flow kappa)
    (hcompact : IsCompact (univ : Set M))
    (hno : NoEmbeddedTrivialNormalProjectivePlane K)
    (hneck : ¬ ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p)
    (hcap : ¬ HasStrongCollarCap K epsilon C p) :
    ∃ B : BasedKappaSolution kappa,
      IsCompact (univ : Set B.carrier.carrier) ∧
      NoEmbeddedTrivialNormalProjectivePlane B.flow ∧
      metricDiameter (B.flow.flow.metric 0) univ =
        Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) univ ∧
      (¬ ∃ N : StrongEvolvingNeck B.flow 0 epsilon, N.center = B.base) ∧
      ¬ HasStrongCollarCap B.flow epsilon C B.base := by
  let L : AncientKappaSolution 3 M := {
    K with kappa := kappa, kappa_pos := hkappa, noncollapsed := hnc }
  obtain ⟨N⟩ := P.normalization M L p 0 le_rfl
  have htarget : AncientKappaNoncollapsed N.target.flow kappa := by
    have hk : N.target.kappa = kappa := N.target_kappa
    rw [← hk]
    exact N.target.noncollapsed
  let B := N.target.toSmallBased p hkappa htarget N.normalized_scalar
  refine ⟨B, N.target.toSmallBased_isCompact p hkappa htarget
    N.normalized_scalar hcompact,
    N.target.toSmallBased_noEmbeddedTrivialNormalProjectivePlane p hkappa htarget
      N.normalized_scalar hno, ?_, ?_, ?_⟩
  · change metricDiameter (N.target.flow.shrink.metric 0) univ = _
    rw [RicciFlow.metricDiameter_shrink, N.metricDiameter_zero, N.scale_eq]
  · intro h
    obtain ⟨A, hA⟩ := N.target.strongNeck_of_toSmallBased p hkappa htarget
      N.normalized_scalar h
    let A' := N.strongNeckFromNormalization le_rfl A hA
    exact hneck ⟨{ A' with }, rfl⟩
  · intro h
    have ht := hasStrongCollarCap_of_toSmallBased N.target p hkappa htarget
      N.normalized_scalar h
    obtain ⟨A, hε, hC, hp, hcollar⟩ := hasStrongCollarCap_fromNormalization N ht
    apply hcap
    refine ⟨A, hε, hC, hp, ?_⟩
    intro x hx hxcore
    obtain ⟨Q, hQ⟩ := hcollar x hx hxcore
    exact ⟨{ Q with }, hQ⟩



theorem exists_normalized_bad_neighborhood_sequence_strong_collars_of_m27
    (P : M27KappaAlternativePredecessors.{u})
    {kappa epsilon C : ℝ} (hkappa : 0 < kappa)
    (hbad : ¬ ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa → IsCompact (univ : Set M) →
        NoEmbeddedTrivialNormalProjectivePlane K →
        D < Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) univ →
        (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
        HasStrongCollarCap K epsilon C p) :
    ∃ S : NormalizedKappaSolutionSequence kappa,
      (∀ k, IsCompact (univ : Set (S.term k).carrier.carrier)) ∧
      (∀ k, NoEmbeddedTrivialNormalProjectivePlane (S.term k).flow) ∧
      Tendsto (fun k => metricDiameter ((S.term k).flow.flow.metric 0) univ) atTop atTop ∧
      (∀ k, ¬ ∃ N : StrongEvolvingNeck (S.term k).flow 0 epsilon,
        N.center = (S.term k).base) ∧
      (∀ k, ¬ HasStrongCollarCap (S.term k).flow epsilon C (S.term k).base) := by
  classical
  have hsmall (D : ℝ) (hD : 0 < D) : ∃ B : BasedKappaSolution kappa,
      IsCompact (univ : Set B.carrier.carrier) ∧
      NoEmbeddedTrivialNormalProjectivePlane B.flow ∧
      D < metricDiameter (B.flow.flow.metric 0) univ ∧
      (¬ ∃ N : StrongEvolvingNeck B.flow 0 epsilon, N.center = B.base) ∧
      ¬ HasStrongCollarCap B.flow epsilon C B.base := by
    by_contra h
    apply hbad
    refine ⟨D, hD, ?_⟩
    intro M _ _ _ _ _ _ _ _ _ K p hnc hcompact hno hdiam
    by_contra hnone
    rw [not_or] at hnone
    obtain ⟨B, hB, hBno, hscale, hneck, hcap⟩ :=
      exists_smallBased_without_neighborhoods_strong_collars_of_m27 P hkappa K p hnc
        hcompact hno hnone.1 hnone.2
    exact h ⟨B, hB, hBno, hscale ▸ hdiam, hneck, hcap⟩
  choose B hcompact hno hdiam hneck hcap using
    (fun k : ℕ => hsmall ((k : ℝ) + 1) (by positivity))
  let S : NormalizedKappaSolutionSequence kappa := ⟨hkappa, B⟩
  refine ⟨S, hcompact, hno, ?_, hneck, hcap⟩
  apply tendsto_atTop_mono (fun k : ℕ =>
    (show (k : ℝ) ≤ (k : ℝ) + 1 by linarith).trans (hdiam k).le)
  exact tendsto_natCast_atTop_atTop

end PoincareConjecture
