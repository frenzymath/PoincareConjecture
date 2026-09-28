import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialSphereGraph
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphSide
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CollarGraphComponentLabels











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





theorem initial_sphere_isSeparating (H : CounterexampleNeckFamily E)
    (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j : ℕ), L.carrier ⊆ G.exhaustion j →
      (∀ᶠ k in atTop, j ≤ k ∧ ∃ f : UnitTwoSphere → ℝ,
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
        (∀ q, |f q| < epsilon⁻¹ / 32) ∧
        (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
          W.high_index G k) '' L.central_sphere =
            range (fun q : UnitTwoSphere =>
              ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map
                (q, f q))) → L.IsSeparating := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  let : LocallyPathConnectedSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  intro L j hLstage hgraphs
  have hzero (q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-L.epsilon⁻¹) L.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr L.epsilon_pos), inv_pos.mpr L.epsilon_pos⟩
  obtain ⟨x₀, hx₀⟩ := (L.isConnected_belowGraph_m28 _ continuous_const hzero).nonempty
  obtain ⟨x₁, hx₁⟩ := (L.isConnected_aboveGraph_m28 _ continuous_const hzero).nonempty
  have hx₀S : x₀ ∈ L.central_sphereᶜ := by
    intro hS
    exact (ne_of_lt hx₀.2) ((L.mem_central_sphere_iff_of_mem_carrier hx₀.1).mp hS)
  have hx₁S : x₁ ∈ L.central_sphereᶜ := by
    intro hS
    exact (ne_of_gt hx₁.2) ((L.mem_central_sphere_iff_of_mem_carrier hx₁.1).mp hS)
  let e := fun k => H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
    W.high_index G k
  let T := fun k => (W.tube (W.high_index (G.subsequence k))).tube.carrier
  have hesource (k : ℕ) : (e k).source = G.exhaustion k :=
    H.regularRawStageDiffeomorph_source _ _ _ _ _ k
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  have hmap (k : ℕ) : MapsTo (e k) (G.exhaustion k) (T k) := by
    intro x _
    exact (G.embedding k x).val.property
  have hlabels : ∀ᶠ k in atTop, ∃ F,
      (∀ z ∈ F, connectedComponentIn (T k \ (e k) '' L.central_sphere) z = F) ∧
      (e k x₀ ∈ F ↔ e k x₁ ∉ F) := by
    filter_upwards [hgraphs] with k hk
    obtain ⟨hjk, f, hf, hheight, hsphere⟩ := hk
    let N := ((W.tube (W.high_index (G.subsequence k))).list.node 0).2
    change (e k) '' L.central_sphere = range (fun q => N.coordinate_map (q, f q))
      at hsphere
    have heps : N.epsilon = epsilon :=
      (W.tube (W.high_index (G.subsequence k))).initial_node_geometry.1
    have hepspos : 0 < epsilon := heps ▸ N.epsilon_pos
    have hdom (q : UnitTwoSphere) : f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [heps]
      have h := abs_lt.mp (hheight q)
      constructor <;> linarith [h.1, h.2, inv_pos.mpr hepspos]
    have hcomponent :=
      ((W.tube (W.high_index (G.subsequence k))).initial_graph_negative_region
        f hf.continuous hheight).2.2
    refine ⟨N.belowGraph_m28 f, ?_, ?_⟩
    · rw [hsphere]
      exact hcomponent
    · apply neck_collar_opposite_graph_component_labels L N (e k).toOpenPartialHomeomorph
        (by change L.carrier ⊆ (e k).source
            rw [hesource]
            exact hLstage.trans (hmono hjk))
        (fun _ hx => hmap k (hmono hjk (hLstage hx))) f hdom hsphere hcomponent hx₀ hx₁
  have hnopath : ¬ JoinedIn L.central_sphereᶜ x₀ x₁ :=
    not_joinedIn_of_eventually_opposite_component_labels G.exhaustion G.exhaustion_open
      hmono G.exhaustion_covers (L.central_sphere_subset.trans hLstage)
      (fun k => e k) T
      (fun k => by simpa only [hesource] using (e k).contMDiffOn.continuousOn)
      (fun k => by simpa only [hesource] using (e k).toPartialEquiv.injOn)
      hmap hlabels
  have hcomponent : connectedComponent L.center = univ := by
    apply Subset.antisymm (subset_univ _)
    exact G.limitCarrier.connected.isPreconnected.subset_connectedComponent (mem_univ _)
  change (connectedComponent L.center \ L.central_sphere).Nonempty ∧
    ¬ IsConnected (connectedComponent L.center \ L.central_sphere)
  rw [hcomponent, ← compl_eq_univ_sdiff]
  refine ⟨⟨x₀, hx₀S⟩, ?_⟩
  intro hconn
  exact hnopath ((L.isClosed_central_sphere.isOpen_compl.isConnected_iff_isPathConnected.mp
    hconn).joinedIn x₀ hx₀S x₁ hx₁S)

set_option maxHeartbeats 2400000 in





theorem exists_retained_initial_separating_sphere_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
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
          ∀ D₀ : LeviCivitaData G.limitMetric,
            ∃ j : ℕ, ∃ L : EpsilonNeck G.limitMetric,
              L.epsilon = 3 * epsilon / 2 ∧ L.center = G.base ∧
              L.scale = (4 * max C 2)⁻¹ ∧ L.connection = D₀ ∧
              L.carrier ⊆ G.exhaustion j ∧ L.IsSeparating ∧
              ∀ᶠ k in atTop, j ≤ k ∧ ∃ f : UnitTwoSphere → ℝ,
                ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
                (∀ q, |f q| < epsilon⁻¹ / 32) ∧
                (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G k) '' L.central_sphere =
                    range (fun q : UnitTwoSphere =>
                      ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map
                        (q, f q)) := by
  obtain ⟨epsilon₀, hpos, hsmall, hgraph⟩ := exists_retained_initial_sphere_graph_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  obtain ⟨j, L, heps, hcenter, hscale, hconnection, hstage, htail⟩ :=
    hgraph H hepsilon W G D₀
  exact ⟨j, L, heps, hcenter, hscale, hconnection, hstage,
    H.initial_sphere_isSeparating W G L j hstage htail, htail⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
