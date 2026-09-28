import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.SmallBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

section CoreVolume

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem AncientKappaSolution.scalarCoreRadius_volume_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) {kappa t : ℝ}
    (hnoncollapse : AncientKappaNoncollapsed K.flow kappa)
    (ht : t ≤ 0) (hpos : ∀ x, 0 < (K.flow.connection t).scalarCurvature x) (p : M) :
    let r := scalarCoreRadius (K.flow.metric t) (K.flow.connection t) (K.complete t ht) hpos p
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball p r) := by
  have hr := scalarCoreRadius_spec (K.flow.metric t) (K.flow.connection t) (K.complete t ht) hpos p
  exact scalar_radius_volume_lower P K hnoncollapse ht p hr.1 hr.2.le

end CoreVolume

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

theorem exists_transferred_core_volume_threshold
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ kappa : ℝ, 0 < kappa → ∃ C : ℝ, 0 < C ∧
        ∀ {S : NormalizedKappaSolutionSequence kappa}
          {G : M23InteriorConvergence S}
          {e : ∀ j, NormalizedKappaSpacetimeEmbedding
            (source := S.term (G.subsequence j)) (target := G.limit)
            (Iic 0 ×ˢ G.exhaustion j)},
          M23TerminalMetricConvergence G e →
          (∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
            ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2) →
          ∀ A : CapCertificate (G.limit.flow.flow.metric 0), A.epsilon ≤ epsilon₀ →
            ∀ᶠ k in atTop,
              ∃ radius : (S.term (G.subsequence k)).carrier.carrier → ℝ,
                (∀ y ∈ (fun x ↦ ((e k).toFun (0, x)).2) '' A.closed_core,
                  0 < radius y ∧
                  scalarCurvatureSupOn ((S.term (G.subsequence k)).flow.flow.metric 0)
                    ((S.term (G.subsequence k)).flow.flow.connection 0)
                    (((S.term (G.subsequence k)).flow.flow.metric 0).ball y (radius y)) =
                      (radius y)⁻¹ ^ 2 ∧
                  closure (((S.term (G.subsequence k)).flow.flow.metric 0).ball y (radius y)) ⊆
                    (fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier ∧
                  IsCompact (closure
                    (((S.term (G.subsequence k)).flow.flow.metric 0).ball y (radius y))) ∧
                  ENNReal.ofReal (kappa * radius y ^ 3) ≤
                    calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
                      ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier)) ∧
                ∃ bound : ℝ, C⁻¹ < bound ∧
                  ∀ y ∈ (fun x ↦ ((e k).toFun (0, x)).2) '' A.closed_core,
                    ENNReal.ofReal (bound * radius y ^ 3) ≤
                      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
                        (((S.term (G.subsequence k)).flow.flow.metric 0).ball y (radius y)) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, htransport⟩ := exists_cap_core_ball_transport_threshold
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro kappa hkappa
  let C := 2 / kappa
  have hC : 0 < C := div_pos (by norm_num) hkappa
  have hCinv : C⁻¹ < kappa := by
    have heq : C⁻¹ = kappa / 2 := by dsimp [C]; simp
    rw [heq]
    linarith
  refine ⟨C, hC, ?_⟩
  intro S G e hconv hfixed A hepsilon
  have hlimit (x : G.limit.carrier.carrier) :
      0 < (G.limit.flow.flow.connection 0).scalarCurvature x :=
    P.scalar_pos_small G.limit.flow 0 le_rfl x
  have hsource (k : ℕ) (x : (S.term (G.subsequence k)).carrier.carrier) :
      0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature x :=
    P.scalar_pos_small (S.term (G.subsequence k)).flow 0 le_rfl x
  filter_upwards [htransport hconv hfixed hlimit hsource A hepsilon] with k hk
  let B := S.term (G.subsequence k)
  let g := B.flow.flow.metric 0
  let D := B.flow.flow.connection 0
  let radius := scalarCoreRadius g D (B.flow.complete 0 le_rfl) (hsource k)
  have hr (y : B.carrier.carrier) : 0 < radius y ∧
      scalarCurvatureSupOn g D (g.ball y (radius y)) = (radius y)⁻¹ ^ 2 :=
    scalarCoreRadius_spec g D (B.flow.complete 0 le_rfl) (hsource k) y
  have hnc : AncientKappaNoncollapsed B.flow.flow kappa := by
    simpa only [B.kappa_eq] using B.flow.noncollapsed
  have hv (y : B.carrier.carrier) : ENNReal.ofReal (kappa * radius y ^ 3) ≤
      calibratedMetricVolume g (g.ball y (radius y)) :=
    scalar_radius_volume_lower_small P B.flow hnc le_rfl y (hr y).1 (hr y).2.le
  refine ⟨radius, ?_, kappa, hCinv, fun y _ ↦ hv y⟩
  rintro y ⟨p, hp, rfl⟩
  have hsubset := hk p hp
  exact ⟨(hr _).1, (hr _).2, hsubset,
    g.isCompact_closure_ball_of_metricComplete (B.flow.complete 0 le_rfl) _ _,
    (hv _).trans (MeasureTheory.measure_mono (subset_closure.trans hsubset))⟩

end M23TerminalMetricConvergence

end PoincareConjecture
