import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Transition

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, Nonempty (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))

include hD he hc hlower hopen hconn in
theorem exists_source_transition_neighborhood {i j : ι} {x : X i}
    (hx : x ∈ overlap D i j) :
    ∃ U : Set (X i), IsOpen U ∧ x ∈ U ∧ ∃ K : Set (X j), IsCompact K ∧
      ∀ᶠ k in atTop, ∀ x' ∈ U,
        e k i x' ∈ e k j '' K ∧ Function.invFun (e k j) (e k i x') ∈ K := by
  classical
  obtain ⟨y, hxy⟩ := hx
  obtain ⟨r, hr, hK⟩ := exists_isCompact_closedBall y
  let δ : ℝ := (c j * r / 2) / ((L i : ℝ) + 1)
  have hδ : 0 < δ := div_pos (half_pos (mul_pos (hc j) hr)) (by positivity)
  refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, closedBall y r, hK, ?_⟩
  have hnear : ∀ᶠ k in atTop, dist (e k i x) (e k j y) < c j * r / 2 := by
    have hlim := hD i j x y
    rw [hxy] at hlim
    exact hlim.eventually (gt_mem_nhds (half_pos (mul_pos (hc j) hr)))
  filter_upwards [hnear] with k hk x' hx'
  have hdist : dist (e k i x') (e k j y) < c j * r := by
    have hnear' : ((L i : ℝ) + 1) * dist x' x < c j * r / 2 := by
      have := (lt_div_iff₀ (by positivity : 0 < (L i : ℝ) + 1)).mp hx'
      simpa only [mul_comm] using this
    have htri := dist_triangle (e k i x') (e k i x) (e k j y)
    have hupper := (he k i).dist_le_mul x' x
    nlinarith [dist_nonneg (x := x') (y := x)]
  have himage : e k i x' ∈ e k j '' closedBall y r :=
    image_mono ball_subset_closedBall
      (ball_subset_image_of_lower_bound (hopen k j) hr hK
        (fun z => hlower k j z y) (hconn k _ _) (hc j) hdist)
  refine ⟨himage, ?_⟩
  obtain ⟨z, hz, heq⟩ := himage
  rw [← heq, Function.leftInverse_invFun (hopen k j).injective]
  exact hz

include hD he hc hlower hopen hconn in
theorem exists_compact_source_transition_target {i j : ι} {C : Set (X i)}
    (hC : IsCompact C) (hCoverlap : C ⊆ overlap D i j) :
    ∃ K : Set (X j), IsCompact K ∧ ∀ᶠ k in atTop, ∀ x ∈ C,
      e k i x ∈ e k j '' K ∧ Function.invFun (e k j) (e k i x) ∈ K := by
  refine hC.induction_on (p := fun S => ∃ K : Set (X j), IsCompact K ∧
    ∀ᶠ k in atTop, ∀ x ∈ S,
      e k i x ∈ e k j '' K ∧ Function.invFun (e k j) (e k i x) ∈ K) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, Eventually.of_forall (by simp)⟩
  · intro S T hST hT
    obtain ⟨K, hK, hrep⟩ := hT
    exact ⟨K, hK, hrep.mono fun k hk x hx => hk x (hST hx)⟩
  · intro S T hS hT
    obtain ⟨K, hK, hrepK⟩ := hS
    obtain ⟨K', hK', hrepK'⟩ := hT
    refine ⟨K ∪ K', hK.union hK', ?_⟩
    filter_upwards [hrepK, hrepK'] with k hk hk' x hx
    rcases hx with hx | hx
    · exact ⟨image_mono subset_union_left (hk x hx).1,
        Or.inl (hk x hx).2⟩
    · exact ⟨image_mono subset_union_right (hk' x hx).1,
        Or.inr (hk' x hx).2⟩
  · intro x hx
    obtain ⟨U, hU, hxU, K, hK, hrep⟩ :=
      exists_source_transition_neighborhood hD L he c hc hlower hopen hconn (hCoverlap hx)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU), K, hK, hrep⟩

include hD he hc hlower hopen hconn in
theorem tendsto_source_transition {i j : ι} {x : X i}
    (hx : x ∈ overlap D i j) :
    Tendsto (fun k => Function.invFun (e k j) (e k i x)) atTop
      (𝓝 (transition D i j x)) := by
  obtain ⟨U, _, hxU, K, _, hK⟩ :=
    exists_source_transition_neighborhood hD L he c hc hlower hopen hconn hx
  have hlim := hD i j x (transition D i j x)
  rw [transition_zero D hx] at hlim
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _
    (show Tendsto (fun k => dist (e k i x) (e k j (transition D i j x)) / c j)
      atTop (𝓝 0) from by simpa using hlim.div_const (c j))
  filter_upwards [hK] with k hk
  have himage : e k i x ∈ range (e k j) := image_subset_range _ _ (hk x hxU).1
  have h := hlower k j (Function.invFun (e k j) (e k i x)) (transition D i j x)
  rw [Function.invFun_eq himage] at h
  exact (le_div_iff₀ (hc j)).2 (by simpa only [mul_comm] using h)

include hD he hc hlower hopen hconn in
theorem tendstoLocallyUniformlyOn_source_transition
    (hlocal : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (i j : ι) :
    TendstoLocallyUniformlyOn (fun k x => Function.invFun (e k j) (e k i x))
      (transition D i j) atTop (overlap D i j) := by
  have hgraph := (hlocal i j).tendstoLocallyUniformlyOn.comp
    (fun x => (x, transition D i j x)) (mapsTo_univ _ _)
    (continuousOn_id.prodMk (lipschitzOn_transition hD L he c hc hlower i j).continuousOn)
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε x hx
  obtain ⟨U, hU, hxU, K, _, hK⟩ :=
    exists_source_transition_neighborhood hD L he c hc hlower hopen hconn hx
  obtain ⟨V, hV, hconv⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp hgraph
    (c j * ε) (mul_pos (hc j) hε) x hx
  refine ⟨V ∩ U ∩ overlap D i j,
    inter_mem (inter_mem hV (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)))
      self_mem_nhdsWithin, ?_⟩
  filter_upwards [hconv, hK] with k hk hrep z hz
  have hrange : e k i z ∈ range (e k j) := image_subset_range _ _ (hrep z hz.1.2).1
  have hbound := hlower k j (transition D i j z) (Function.invFun (e k j) (e k i z))
  rw [Function.invFun_eq hrange, dist_comm (e k j _)] at hbound
  have hsmall := hk z hz.1.1
  change dist (D i j (z, transition D i j z))
    (dist (e k i z) (e k j (transition D i j z))) < c j * ε at hsmall
  rw [transition_zero D hz.2, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg dist_nonneg] at hsmall
  exact (mul_lt_mul_iff_right₀ (hc j)).mp (hbound.trans_lt hsmall)

end PoincareConjecture.ChartDistance
