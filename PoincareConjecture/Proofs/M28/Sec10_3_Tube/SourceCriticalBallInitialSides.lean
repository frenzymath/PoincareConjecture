import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialSideBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in






theorem exists_retained_initial_sides_accuracy :
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
              ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
              ∃ Uminus Uplus : Set G.limitCarrier.carrier,
                IsOpen Uminus ∧ IsOpen Uplus ∧ IsConnected Uminus ∧ IsConnected Uplus ∧
                Disjoint Uminus Uplus ∧ Uminus ∪ Uplus = L.central_sphereᶜ ∧
                frontier Uminus = L.central_sphere ∧ frontier Uplus = L.central_sphere ∧
                closure Uminus = Uminus ∪ L.central_sphere ∧
                closure Uplus = Uplus ∪ L.central_sphere ∧
                (∀ x ∈ Uminus, D₀.scalarCurvature x ≤ 32 * (max C 2) ^ 2) ∧
                ∃ f : ℕ → UnitTwoSphere → ℝ,
                  (∀ k, j ≤ sigma k ∧ ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k) ∧
                    (∀ q, |f k q| < epsilon⁻¹ / 32) ∧
                    (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                      W.high_index G (sigma k)) '' L.central_sphere =
                        range (fun q : UnitTwoSphere =>
                          ((W.tube (W.high_index
                            (G.subsequence (sigma k)))).list.node 0).2.coordinate_map (q, f k q))) ∧
                  (∀ x ∈ Uminus, ∀ᶠ k in atTop,
                    H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                      W.high_index G (sigma k) x ∈
                        ((W.tube (W.high_index
                          (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (f k)) ∧
                  (∀ x ∈ Uplus, ∀ᶠ k in atTop,
                    H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                      W.high_index G (sigma k) x ∉
                        ((W.tube (W.high_index
                          (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28 (f k)) := by
  obtain ⟨epsilonS, hSpos, hSsmall, hsphere⟩ :=
    exists_retained_initial_separating_sphere_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hscalar⟩ := exists_initial_limit_scalar_upper_accuracy.{u}
  refine ⟨min epsilonS epsilonR, lt_min hSpos hRpos,
    (min_le_left _ _).trans hSsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  let : ConnectedSpace G.limitCarrier.carrier :=
    connectedSpace_iff_univ.mpr G.limitCarrier.connected
  intro D₀
  obtain ⟨j, L, heps, hcenter, hscale, hconnection, hstage, hsep, htail⟩ :=
    hsphere H (hepsilon.trans (min_le_left _ _)) W G D₀
  obtain ⟨sigma, hsigma, a, b, horientation, f, hf⟩ :=
    H.exists_retained_initial_graph_orientation W G L j hstage htail
  let Uminus := connectedComponentIn L.central_sphereᶜ a
  let Uplus := connectedComponentIn L.central_sphereᶜ b
  have hgraphs (k : ℕ) : Continuous (f k) ∧ (∀ q, |f k q| < epsilon⁻¹ / 32) ∧
      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k)) '' L.central_sphere =
          range (fun q : UnitTwoSphere =>
            ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
              (q, f k q)) :=
    ⟨(hf k).2.1.continuous, (hf k).2.2.1, (hf k).2.2.2.1⟩
  have hminus (x : G.limitCarrier.carrier) (hx : x ∈ Uminus) : ∀ᶠ k in atTop,
      H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k) x ∈
          ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
            (f k) := by
    filter_upwards [H.eventually_initial_graph_labels_on_component W G L j hstage
      hsigma f hgraphs hx] with k hk
    exact hk.mp (hf k).2.2.2.2.1
  have hplus (x : G.limitCarrier.carrier) (hx : x ∈ Uplus) : ∀ᶠ k in atTop,
      H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma k) x ∉
          ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
            (f k) := by
    filter_upwards [H.eventually_initial_graph_labels_on_component W G L j hstage
      hsigma f hgraphs hx] with k hk
    exact fun hxF => (hf k).2.2.2.2.2 (hk.mpr hxF)
  have hgeometry : IsOpen Uminus ∧ IsOpen Uplus ∧ IsConnected Uminus ∧
      IsConnected Uplus ∧ Disjoint Uminus Uplus ∧ Uminus ∪ Uplus = L.central_sphereᶜ ∧
      frontier Uminus = L.central_sphere ∧ frontier Uplus = L.central_sphere ∧
      closure Uminus = Uminus ∪ L.central_sphere ∧
      closure Uplus = Uplus ∪ L.central_sphere := by
    rcases horientation with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · obtain ⟨hopen₀, hopen₁, hconn₀, hconn₁, hdisj, hcover, hf₀, hf₁, hc₀, hc₁, _, _⟩ :=
        L.complement_components_of_isSeparating hsep ha hb
      exact ⟨hopen₀, hopen₁, hconn₀, hconn₁, hdisj, hcover, hf₀, hf₁, hc₀, hc₁⟩
    · obtain ⟨hopen₁, hopen₀, hconn₁, hconn₀, hdisj, hcover, hf₁, hf₀, hc₁, hc₀, _, _⟩ :=
        L.complement_components_of_isSeparating hsep hb ha
      exact ⟨hopen₀, hopen₁, hconn₀, hconn₁, hdisj.symm,
        (union_comm _ _).trans hcover, hf₀, hf₁, hc₀, hc₁⟩
  obtain ⟨hopen₀, hopen₁, hconn₀, hconn₁, hdisj, hcover, hf₀, hf₁, hc₀, hc₁⟩ := hgeometry
  refine ⟨j, L, heps, hcenter, hscale, hconnection, hstage, hsep, sigma, hsigma,
    Uminus, Uplus, hopen₀, hopen₁, hconn₀, hconn₁, hdisj, hcover, hf₀, hf₁, hc₀, hc₁,
    ?_, f, ?_, hminus, hplus⟩
  · intro x hx
    apply hscalar H (hepsilon.trans (min_le_right _ _)) W G D₀ sigma hsigma x
    exact (hminus x hx).mono fun _ hk => hk.1
  · intro k
    exact ⟨(hf k).1, (hf k).2.1, (hf k).2.2.1, (hf k).2.2.2.1⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
