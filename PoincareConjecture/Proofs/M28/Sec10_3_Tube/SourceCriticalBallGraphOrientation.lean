import PoincareConjecture.Proofs.M28.Mathlib.RetainedWitnessLabel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallGraphLabels

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

theorem exists_retained_initial_graph_orientation (H : CounterexampleNeckFamily E)
    (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j : ℕ), L.carrier ⊆ G.exhaustion j →
      (∀ᶠ k in atTop, j ≤ k ∧ ∃ f : UnitTwoSphere → ℝ,
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧ (∀ q, |f q| < epsilon⁻¹ / 32) ∧
        (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
          W.high_index G k) '' L.central_sphere =
            range (fun q : UnitTwoSphere =>
              ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map
                (q, f q))) →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ xminus xplus : G.limitCarrier.carrier,
        ((xminus ∈ L.belowGraph_m28 (fun _ => 0) ∧ xplus ∈ L.aboveGraph_m28 (fun _ => 0)) ∨
          (xplus ∈ L.belowGraph_m28 (fun _ => 0) ∧ xminus ∈ L.aboveGraph_m28 (fun _ => 0))) ∧
        ∃ f : ℕ → UnitTwoSphere → ℝ, ∀ k,
          j ≤ sigma k ∧ ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k) ∧
          (∀ q, |f k q| < epsilon⁻¹ / 32) ∧
          (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k)) '' L.central_sphere =
              range (fun q : UnitTwoSphere =>
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                  (q, f k q)) ∧
          H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k) xminus ∈
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                (f k) ∧
          H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma k) xplus ∉
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                (f k) := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro L j hstage hgraphs
  have hzero (q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-L.epsilon⁻¹) L.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr L.epsilon_pos), inv_pos.mpr L.epsilon_pos⟩
  obtain ⟨x₀, hx₀⟩ := (L.isConnected_belowGraph_m28 _ continuous_const hzero).nonempty
  obtain ⟨x₁, hx₁⟩ := (L.isConnected_aboveGraph_m28 _ continuous_const hzero).nonempty
  let P := fun k (f : UnitTwoSphere → ℝ) =>
    j ≤ k ∧ ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧ (∀ q, |f q| < epsilon⁻¹ / 32) ∧
      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G k) '' L.central_sphere =
          range (fun q : UnitTwoSphere =>
            ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map (q, f q))
  let label := fun k (f : UnitTwoSphere → ℝ) =>
    H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k x₀ ∈
      ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.belowGraph_m28 f
  have hgood : ∀ᶠ k in atTop, ∃ f, P k f := by
    filter_upwards [hgraphs] with k hk
    obtain ⟨hjk, f, hf, hheight, hsphere⟩ := hk
    exact ⟨f, hjk, hf, hheight, hsphere⟩
  obtain ⟨sigma, hsigma, f, hf, hlabel⟩ :=
    Filter.exists_strictMono_constant_label_witness P label hgood
  have hopposite (k : ℕ) := H.initial_graph_opposite_labels W G L j (sigma k)
    hstage (hf k).1 (f k) (hf k).2.1.continuous (hf k).2.2.1 (hf k).2.2.2
    x₀ hx₀ x₁ hx₁
  rcases hlabel with hnegative | hpositive
  · refine ⟨sigma, hsigma, x₀, x₁, Or.inl ⟨hx₀, hx₁⟩, f, ?_⟩
    intro k
    exact ⟨(hf k).1, (hf k).2.1, (hf k).2.2.1, (hf k).2.2.2,
      hnegative k, (hopposite k).mp (hnegative k)⟩
  · refine ⟨sigma, hsigma, x₁, x₀, Or.inr ⟨hx₀, hx₁⟩, f, ?_⟩
    intro k
    refine ⟨(hf k).1, (hf k).2.1, (hf k).2.2.1, (hf k).2.2.2, ?_, hpositive k⟩
    by_contra hnot
    exact hpositive k ((hopposite k).mpr hnot)

end PoincareConjecture.M28.CounterexampleNeckFamily
