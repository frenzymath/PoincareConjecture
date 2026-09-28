import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallGraphOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SeparatingNeckComponents
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialScalar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 2400000 in





theorem eventually_initial_graph_labels_on_component (H : CounterexampleNeckFamily E)
    (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j : ℕ), L.carrier ⊆ G.exhaustion j →
      ∀ {sigma : ℕ → ℕ}, StrictMono sigma →
      ∀ (f : ℕ → UnitTwoSphere → ℝ),
      (∀ k, Continuous (f k) ∧ (∀ q, |f k q| < epsilon⁻¹ / 32) ∧
        (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
          W.high_index G (sigma k)) '' L.central_sphere =
            range (fun q : UnitTwoSphere =>
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                (q, f k q))) →
      ∀ {a x : G.limitCarrier.carrier}, x ∈ connectedComponentIn L.central_sphereᶜ a →
        ∀ᶠ k in atTop,
          H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k) a ∈
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                (f k) ↔
          H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k) x ∈
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                (f k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  let : LocallyPathConnectedSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  intro L j hstage sigma hsigma f hf a x hx
  have ha : a ∈ L.central_sphereᶜ := connectedComponentIn_nonempty_iff.mp ⟨x, hx⟩
  have hopen : IsOpen (connectedComponentIn L.central_sphereᶜ a) :=
    L.isClosed_central_sphere.isOpen_compl.connectedComponentIn
  have hconn : IsConnected (connectedComponentIn L.central_sphereᶜ a) :=
    isConnected_connectedComponentIn_iff.mpr ha
  have hpath : JoinedIn L.central_sphereᶜ a x :=
    ((hopen.isConnected_iff_isPathConnected.mp hconn).joinedIn a
      (mem_connectedComponentIn ha) x hx).mono (connectedComponentIn_subset _ _)
  exact H.eventually_initial_graph_labels_along_path W G L j hstage hsigma f hf hpath

set_option maxHeartbeats 2400000 in





theorem exists_initial_limit_scalar_upper_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∀ (W : CriticalBallSourcePacket H)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D₀ : LeviCivitaData G.limitMetric) (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ x : G.limitCarrier.carrier,
              (∀ᶠ k in atTop,
                H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G (sigma k) x ∈
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.carrier) →
              D₀.scalarCurvature x ≤ 32 * (max C 2) ^ 2 := by
  obtain ⟨epsilon₀, hpos, hsmall, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ sigma hsigma x hx
  let D (k : ℕ) : LeviCivitaData (H.tubeCriticalMetric W.tube W.radius (W.high_index k)) :=
    Classical.choice (exists_leviCivitaData _)
  apply le_of_tendsto ((G.tendsto_scalarCurvature D D₀ x).comp hsigma.tendsto_atTop)
  filter_upwards [hx] with k hk
  let i := W.high_index (G.subsequence (sigma k))
  let N := ((W.tube i).list.node 0).2
  let y := (G.embedding (sigma k) x).val.val
  have hNsmall : N.epsilon ≤ epsilon₀ :=
    (W.tube i).initial_node_geometry.1.trans_le hepsilon
  have hbound := hratio ((E (i + H.shift)).flow.slice (E (i + H.shift)).time).carrier
    ((E (i + H.shift)).flow.metric (E (i + H.shift)).time)
    ((E (i + H.shift)).flow.connection (E (i + H.shift)).time) N hNsmall y hk
    N.center (N.central_sphere_subset N.center_on_central_sphere)
  change (E (i + H.shift)).flow.scalar ⟨(E (i + H.shift)).time, y⟩ ≤
    2 * (E (i + H.shift)).flow.scalar ⟨(E (i + H.shift)).time, N.center⟩ at hbound
  rw [(W.tube i).node_zero_readout.2.2, (H.segment i).lower_scalar] at hbound
  change (D (G.subsequence (sigma k))).scalarCurvature (G.embedding (sigma k) x) ≤ _
  rw [H.tubeCritical_scalar_eq]
  apply (div_le_iff₀ (H.base_scalar_pos i)).mpr
  nlinarith only [hbound]

end PoincareConjecture.M28.CounterexampleNeckFamily
