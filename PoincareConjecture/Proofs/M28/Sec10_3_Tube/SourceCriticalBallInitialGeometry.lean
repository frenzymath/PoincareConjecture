import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawStage
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialNodeCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialScalar
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.PartialDiffeomorphPullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open PoincareConjecture.Proofs.M28.NeckTransfer

set_option maxHeartbeats 2400000 in





theorem exists_retained_initial_geometry_accuracy :
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
          ∀ D₀ : LeviCivitaData G.limitMetric, ∃ j : ℕ, ∀ᶠ k in atTop,
            j ≤ k ∧ ∃ V : NeckGeometryCore G.limitMetric (3 * epsilon / 2),
              V.center = G.base ∧ V.scale = (4 * max C 2)⁻¹ ∧ V.connection = D₀ ∧
              V.carrier ⊆ G.exhaustion j ∧ ∀ z : RoundCylinderSpace,
                V.coordinate_map z =
                  (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                    W.high_index G k).symm
                      (((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map
                        z) := by
  obtain ⟨epsilon₀, hpos, hsmall, hcapture⟩ := exists_retained_initial_node_capture_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  obtain ⟨j, hj⟩ := hcapture H hepsilon W G
  have hepspos : 0 < epsilon :=
    (H.segment 0).cover_epsilon ▸ (H.segment 0).cover.epsilon_pos
  let eta := 3 * epsilon / 2
  have hepseta : epsilon ≤ eta := by dsimp only [eta]; linarith
  have hetahalf : eta < 1 / 2 := by dsimp only [eta]; linarith [hepsilon.trans hsmall]
  have hinv : eta⁻¹ ≤ 3 * epsilon⁻¹ / 4 := by
    have heq : eta⁻¹ = (2 / 3 : ℝ) * epsilon⁻¹ := by
      dsimp only [eta]
      field_simp [hepspos.ne']
    rw [heq]
    nlinarith [inv_pos.mpr hepspos]
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  obtain ⟨hscalar₀, hscale₀⟩ := H.regular_limit_base_scale_eq W.tube W.radius
    W.radius_pos W.high_index G D₀
  refine ⟨j, ?_⟩
  filter_upwards [hj] with k hk
  let i := W.high_index (G.subsequence k)
  let N := ((W.tube i).list.node 0).2
  have hepsN : N.epsilon = epsilon := (W.tube i).initial_node_geometry.1
  have hNeta : N.epsilon ≤ eta := by
    rw [hepsN]
    exact hepseta
  let R := N.restrict_m28 eta hNeta hetahalf
  let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G k
  have hfixed : R.carrier ⊆ (fun x => (G.embedding k x).val.val) '' G.exhaustion j := by
    intro x hx
    change x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ∈ Ioo (-eta⁻¹) eta⁻¹ at hx
    have hheight : |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4 := by
      rw [hepsN]
      exact (abs_lt.mpr hx.2).le.trans hinv
    exact hk.2 x hx.1 hheight
  have hcap : R.carrier ⊆ e.target := by
    rw [H.regularRawStageDiffeomorph_target]
    exact hfixed.trans (image_mono (hmono hk.1))
  have hbase : G.base ∈ e.source := by
    rw [H.regularRawStageDiffeomorph_source]
    exact G.base_in_exhaustion k
  have hcenter : e.symm R.center = G.base := by
    have hraw : R.center = e G.base := by
      change N.center = e G.base
      rw [H.regularRawStageDiffeomorph_base]
      exact (W.tube i).node_zero_readout.2.2
    rw [hraw]
    exact e.left_inv hbase
  have hscalar : 0 < D₀.scalarCurvature (e.symm R.center) := by
    rw [hcenter]
    exact hscalar₀
  let V := pullbackNeckGeometry e R hcap D₀ hscalar
  refine ⟨hk.1, V, hcenter, ?_, rfl, ?_, fun _ => rfl⟩
  · change (D₀.scalarCurvature (e.symm R.center)) ^ (-1 / 2 : ℝ) = _
    rw [hcenter]
    exact hscale₀
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hfixed hy
    have hxe : x ∈ e.source := by
      rw [H.regularRawStageDiffeomorph_source]
      exact hmono hk.1 hx
    have hexy : e x = y := hxy
    have hleft : e.symm (e x) = x := e.left_inv hxe
    rw [← hexy, hleft]
    exact hx

end PoincareConjecture.M28.CounterexampleNeckFamily
