import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Distance
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity










set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem ball_subset_image_of_lower_bound
    {X M : Type*} [MetricSpace X] [MetricSpace M]
    {e : X → M} (he : Topology.IsOpenEmbedding e)
    {x : X} {r c : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closedBall x r))
    (hlower : ∀ y, c * dist y x ≤ dist (e y) (e x))
    (hconn : IsPreconnected (ball (e x) (c * r))) (hc : 0 < c) :
    ball (e x) (c * r) ⊆ e '' ball x r := by
  have hclosed : IsClosed (e '' closedBall x r) :=
    (hcompact.image he.continuous).isClosed
  have hclosure : closure (e '' ball x r) ⊆ e '' closedBall x r :=
    closure_minimal (image_mono ball_subset_closedBall) hclosed
  apply hconn.subset_of_closure_inter_subset (he.isOpenMap _ isOpen_ball)
  · exact ⟨e x, mem_ball_self (mul_pos hc hr), mem_image_of_mem e (mem_ball_self hr)⟩
  · rintro _ ⟨hy, hyball⟩
    obtain ⟨y, hy, rfl⟩ := hclosure hy
    apply mem_image_of_mem
    have h := (hlower y).trans_lt hyball
    exact (mul_lt_mul_iff_right₀ hc).mp h

section Limits

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))

include hD he



theorem exists_zero_of_eventually_mem_image
    {i j : ι} {x : X i} {K : Set (X j)} (hK : IsCompact K) (hne : K.Nonempty)
    (himage : ∀ᶠ k in atTop, e k i x ∈ e k j '' K) :
    ∃ y ∈ K, D i j (x, y) = 0 := by
  classical
  have hchoose (k : ℕ) : ∃ y ∈ K,
      e k i x ∈ e k j '' K → e k j y = e k i x := by
    by_cases hk : e k i x ∈ e k j '' K
    · obtain ⟨y, hy, heq⟩ := hk
      exact ⟨y, hy, fun _ => heq⟩
    · obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, fun h => (hk h).elim⟩
  choose y hy hye using hchoose
  obtain ⟨z, hzK, σ, hσ, hz⟩ := hK.tendsto_subseq hy
  refine ⟨z, hzK, le_antisymm ?_ (nonneg hD i j x z)⟩
  have hlim := (hD i j x z).comp hσ.tendsto_atTop
  have hzero : Tendsto (fun k => (L j : ℝ) * dist (y (σ k)) z) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      (tendsto_iff_dist_tendsto_zero.mp hz)
  apply le_of_tendsto_of_tendsto hlim hzero
  filter_upwards [hσ.tendsto_atTop.eventually himage] with k hk
  dsimp only [Function.comp_apply]
  rw [← hye (σ k) hk]
  exact (he (σ k) j).dist_le_mul _ _



theorem exists_zero_nhds [∀ i, LocallyCompactSpace (X i)]
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {i j : ι} {x : X i} {y : X j} (hxy : D i j (x, y) = 0) :
    ∀ᶠ x' in 𝓝 x, ∃ y' : X j, D i j (x', y') = 0 := by
  obtain ⟨r, hr, hK⟩ := exists_isCompact_closedBall y
  let δ : ℝ := c j * r / ((L i : ℝ) + 1)
  have hδ : 0 < δ := div_pos (mul_pos (hc j) hr) (by positivity)
  filter_upwards [ball_mem_nhds x hδ] with x' hx'
  have hd : D i j (x', y) < c j * r := by
    have htri := triangle hD i i j x' x y
    rw [hxy, add_zero] at htri
    have hu := upper hD L he i x' x
    have hnear : ((L i : ℝ) + 1) * dist x' x < c j * r := by
      have := (lt_div_iff₀ (by positivity : 0 < (L i : ℝ) + 1)).mp hx'
      simpa only [mul_comm] using this
    nlinarith [dist_nonneg (x := x') (y := x)]
  have himage : ∀ᶠ k in atTop, e k i x' ∈ e k j '' closedBall y r := by
    filter_upwards [(hD i j x' y).eventually (gt_mem_nhds hd)] with k hk
    exact image_mono ball_subset_closedBall
      (ball_subset_image_of_lower_bound (hopen k j) hr hK
        (fun z => hlower k j z y) (hconn k _ _) (hc j) hk)
  obtain ⟨y', _, hy'⟩ := exists_zero_of_eventually_mem_image hD L he hK
    ⟨y, mem_closedBall_self hr.le⟩ himage
  exact ⟨y', hy'⟩

end Limits

end PoincareConjecture.ChartDistance
