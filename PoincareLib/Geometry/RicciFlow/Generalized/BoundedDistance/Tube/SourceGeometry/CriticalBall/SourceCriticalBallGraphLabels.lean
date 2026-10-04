import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallInitialSphereSeparation

/-!
# Source component labels along fixed limit paths

The actual initial graph component has opposite collar labels. Every
fixed path in the limiting sphere complement eventually has a single
source label, including after any strict retained selection. Source:
Morgan--Tian Proposition 10.7, pp. 253-254; M28 derivation 114.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 2400000 in
-- The coordinate graph and component live in the original varying raw slice.
/-- A single actual initial graph gives opposite labels to any fixed
collar anchors. All component and strip hypotheses are produced from the
original zero node. Source: Proposition 10.7; M28 derivation 114. -/
theorem initial_graph_opposite_labels (H : CounterexampleNeckFamily E)
    (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j k : ℕ), L.carrier ⊆ G.exhaustion j → j ≤ k →
      ∀ (f : UnitTwoSphere → ℝ), Continuous f → (∀ q, |f q| < epsilon⁻¹ / 32) →
      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k) ''
        L.central_sphere = range (fun q : UnitTwoSphere =>
          ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map (q, f q)) →
      ∀ x₀ ∈ L.belowGraph_m28 (fun _ => 0), ∀ x₁ ∈ L.aboveGraph_m28 (fun _ => 0),
        H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k x₀ ∈
          ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.belowGraph_m28 f ↔
        H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k x₁ ∉
          ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.belowGraph_m28 f := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro L j k hstage hjk f hf hheight hsphere x₀ hx₀ x₁ hx₁
  let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k
  let N := ((W.tube (W.high_index (G.subsequence k))).list.node 0).2
  have heps : N.epsilon = epsilon :=
    (W.tube (W.high_index (G.subsequence k))).initial_node_geometry.1
  have hepspos : 0 < epsilon := heps ▸ N.epsilon_pos
  have hdom (q : UnitTwoSphere) : f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [heps]
    have h := abs_lt.mp (hheight q)
    constructor <;> linarith [h.1, h.2, inv_pos.mpr hepspos]
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  exact neck_collar_opposite_graph_component_labels L N e.toOpenPartialHomeomorph
    (by change L.carrier ⊆ e.source
        rw [H.regularRawStageDiffeomorph_source]
        exact hstage.trans (hmono hjk))
    (fun x _ => (G.embedding k x).val.property) f hdom hsphere
    ((W.tube (W.high_index (G.subsequence k))).initial_graph_negative_region
      f hf hheight).2.2 hx₀ hx₁

set_option maxHeartbeats 2400000 in
-- A common compact stage is chosen before the varying graph and source index.
/-- A fixed path in the actual limit complement eventually has equal
endpoint membership in every retained initial graph component. The
selection remains strict and all source indices are unchanged. Source:
Proposition 10.7, pp. 253-254; M28 derivation 114. -/
theorem eventually_initial_graph_labels_along_path (H : CounterexampleNeckFamily E)
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
      ∀ {x y : G.limitCarrier.carrier}, JoinedIn L.central_sphereᶜ x y →
        ∀ᶠ k in atTop,
          H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k) x ∈
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                (f k) ↔
          H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k) y ∈
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                (f k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro L j hstage sigma hsigma f hf x y hpath
  let e := fun k => H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
    W.high_index G k
  let T := fun k => (W.tube (W.high_index (G.subsequence k))).tube.carrier
  have hesource (k : ℕ) : (e k).source = G.exhaustion k :=
    H.regularRawStageDiffeomorph_source _ _ _ _ _ k
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  have htail := hpath.eventually_component_mem_iff G.exhaustion G.exhaustion_open
    hmono G.exhaustion_covers (L.central_sphere_subset.trans hstage) (fun k => e k) T
    (fun k => by simpa only [hesource] using (e k).contMDiffOn.continuousOn)
    (fun k => by simpa only [hesource] using (e k).toPartialEquiv.injOn)
    (fun k x _ => (G.embedding k x).val.property)
  filter_upwards [hsigma.tendsto_atTop.eventually htail] with k hk
  apply hk
  rw [(hf k).2.2]
  exact ((W.tube (W.high_index (G.subsequence (sigma k)))).initial_graph_negative_region
    (f k) (hf k).1 (hf k).2.1).2.2

end PoincareMT.M28.CounterexampleNeckFamily
