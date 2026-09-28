import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshCapture
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.PartialDiffeomorphPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open PoincareConjecture.Proofs.M28.NeckTransfer

set_option maxHeartbeats 2400000 in

theorem exists_retained_fresh_geometry
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)}
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D0 : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
      0 < D0.scalarCurvature q → epsilon < 1 / 3 →
      ∀ (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (N : ∀ k, EpsilonNeck
        ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time)),
        (∀ k, (N k).epsilon = epsilon) →
        (∀ k, (N k).center = (G.embedding (sigma k) q).val.val) →
        ∀ j : ℕ, (∀ᶠ k in atTop, j ≤ sigma k ∧ ∀ x ∈ (N k).carrier,
          |((N k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
            x ∈ (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j) →
          ∀ᶠ k in atTop, j ≤ sigma k ∧
            ∃ V : NeckGeometryCore G.limitMetric (3 * epsilon / 2),
              V.center = q ∧ V.scale = (D0.scalarCurvature q) ^ (-1 / 2 : ℝ) ∧
              V.connection = D0 ∧ V.carrier ⊆ G.exhaustion j ∧
              ∀ z : RoundCylinderSpace, V.coordinate_map z =
                (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G (sigma k)).symm ((N k).coordinate_map z) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q hscalar hsmall sigma hsigma N heps hcenter j hcapture
  have hepspos : 0 < epsilon := heps 0 ▸ (N 0).epsilon_pos
  let eta := 3 * epsilon / 2
  have hepseta : epsilon ≤ eta := by dsimp only [eta]; linarith
  have hetahalf : eta < 1 / 2 := by dsimp only [eta]; linarith
  have hinv : eta⁻¹ = 2 * epsilon⁻¹ / 3 := by
    dsimp only [eta]
    field_simp [hepspos.ne']
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  obtain ⟨jq, hjq⟩ : ∃ jq, q ∈ G.exhaustion jq := by
    have hq : q ∈ ⋃ jq, G.exhaustion jq := by rw [G.exhaustion_covers]; exact mem_univ _
    exact mem_iUnion.mp hq
  filter_upwards [hcapture, hsigma.tendsto_atTop.eventually (eventually_ge_atTop jq)]
    with k hk hjqk
  have hNeta : (N k).epsilon ≤ eta := by rw [heps]; exact hepseta
  let R := (N k).restrict_m28 eta hNeta hetahalf
  let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
    W.high_index G (sigma k)
  have hfixed : R.carrier ⊆
      (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j := by
    intro x hx
    change x ∈ (N k).carrier ∧
      ((N k).coordinate_inverse x).2 ∈ Ioo (-eta⁻¹) eta⁻¹ at hx
    exact hk.2 x hx.1 ((abs_lt.mpr hx.2).le.trans_eq hinv)
  have hcap : R.carrier ⊆ e.target := by
    rw [H.regularRawStageDiffeomorph_target]
    exact hfixed.trans (image_mono (hmono hk.1))
  have hqs : q ∈ e.source := by
    rw [H.regularRawStageDiffeomorph_source]
    exact hmono hjqk hjq
  have hcenterV : e.symm R.center = q := by
    have hc : R.center = e q := hcenter k
    rw [hc]
    exact e.left_inv hqs
  have hscalarV : 0 < D0.scalarCurvature (e.symm R.center) := by
    rw [hcenterV]
    exact hscalar
  let V := pullbackNeckGeometry e R hcap D0 hscalarV
  refine ⟨hk.1, V, hcenterV, ?_, rfl, ?_, fun _ => rfl⟩
  · change (D0.scalarCurvature (e.symm R.center)) ^ (-1 / 2 : ℝ) = _
    rw [hcenterV]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hfixed hy
    have hxs : x ∈ e.source := by
      rw [H.regularRawStageDiffeomorph_source]
      exact hmono hk.1 hx
    have hxy' : e x = y := hxy
    have hleft : e.symm (e x) = x := e.left_inv hxs
    rw [← hxy', hleft]
    exact hx

end PoincareConjecture.M28.CounterexampleNeckFamily
