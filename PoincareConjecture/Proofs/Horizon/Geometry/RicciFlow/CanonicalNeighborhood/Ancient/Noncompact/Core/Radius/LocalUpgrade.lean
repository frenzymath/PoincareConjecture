import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Normalization.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.StrongNeck

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

theorem noncompact_uniform_strongNeck_of_nearby_neck_of_services
    (P : NoncompactKappaServices.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (_hnoncompact : ¬ IsCompact (univ : Set M))
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0))
        (neck : EpsilonNeck (K.flow.metric 0)) (q : M),
        neck.epsilon ≤ neckSeparationThreshold →
        Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist neck.center q).toReal ≤ 1 →
        Real.sqrt ((K.flow.connection 0).scalarCurvature q) * neck.scale ≤ 2 →
        L < Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist soul.center q).toReal →
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨L, hL, hupgrade⟩ := uniform_strongNeck_of_nearby_neck_and_distant_soul_of_services P
    (kappa := kappa) (B := 2) (Bcenter := 1) hkappa hε hεsmall
    (by norm_num) (by norm_num)
  refine ⟨L, hL, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact soul neck q hsmall hnear hscale hfar
  let : NoncompactSpace M := not_compactSpace_iff.mp fun hcompact =>
    hnoncompact (isCompact_univ_iff.mpr hcompact)
  let K' : AncientKappaSolution 3 M := {
    K with
    kappa := kappa
    kappa_pos := hkappa
    noncollapsed := hnoncollapsed K (K.not_isRound_of_noncompact hnoncompact) }
  obtain ⟨A⟩ := P.normalization M K' q 0 le_rfl
  have htarget : AncientKappaNoncollapsed A.target.flow kappa := by
    have hk : A.target.kappa = kappa := A.target_kappa
    rw [← hk]
    exact A.target.noncollapsed
  let B := A.target.toSmallBased q hkappa htarget A.normalized_scalar
  let soul' := A.target.pointSoulToSmallBased q hkappa htarget A.normalized_scalar
    (A.pointSoul soul)
  obtain ⟨neck', heps, hneckscale, hcenter⟩ := A.exists_epsilonNeck neck
  let neck'' := A.target.epsilonNeckToSmallBased q hkappa htarget A.normalized_scalar neck'
  have hBnoncompact : NoncompactSpace B.carrier.carrier :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).isClosedEmbedding.noncompactSpace
  have hsmall' : neck''.epsilon ≤ neckSeparationThreshold := by
    change neck'.epsilon ≤ neckSeparationThreshold
    rw [heps]
    exact hsmall
  have hnear' : ((B.flow.flow.metric 0).edist neck''.center B.base).toReal ≤ 1 := by
    change ((A.target.flow.shrink.metric 0).edist
      (equivShrink M neck'.center) (equivShrink M q)).toReal ≤ 1
    rw [RicciFlow.shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      A.toReal_edist_zero, hcenter, A.scale_eq]
    exact hnear
  have hscale' : neck''.scale ≤ 2 := by
    change neck'.scale ≤ 2
    rw [hneckscale, A.scale_eq]
    exact hscale
  have hfar' : L < ((B.flow.flow.metric 0).edist soul'.center B.base).toReal := by
    change L < ((A.target.flow.shrink.metric 0).edist
      (equivShrink M soul.center) (equivShrink M q)).toReal
    rw [RicciFlow.shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      A.toReal_edist_zero, A.scale_eq]
    exact hfar
  obtain ⟨N, hN⟩ := A.target.strongNeck_of_toSmallBased q hkappa htarget
    A.normalized_scalar (hupgrade B hBnoncompact soul' neck'' hsmall' hnear' hscale' hfar')
  let N' := A.strongNeckFromNormalization le_rfl N hN
  exact ⟨{ N' with }, rfl⟩

theorem noncompact_uniform_strongNeck_of_nearby_neck
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (_hnoncompact : ¬ IsCompact (univ : Set M))
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0))
        (neck : EpsilonNeck (K.flow.metric 0)) (q : M),
        neck.epsilon ≤ neckSeparationThreshold →
        Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist neck.center q).toReal ≤ 1 →
        Real.sqrt ((K.flow.connection 0).scalarCurvature q) * neck.scale ≤ 2 →
        L < Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist soul.center q).toReal →
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = q := by
  exact noncompact_uniform_strongNeck_of_nearby_neck_of_services P.noncompactServices hε hεsmall

end PoincareConjecture
