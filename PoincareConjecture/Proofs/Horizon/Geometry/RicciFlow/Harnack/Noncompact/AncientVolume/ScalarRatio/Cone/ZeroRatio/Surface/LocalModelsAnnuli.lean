import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Surface.LocalModelsCoverage
import PoincareConjecture.Proofs.Horizon.Topology.Metric.CompactChartNeighborhood









set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem HasLocalSourceModels.eventually_annulus_subset_image
    {n : ℕ} {U : ℕ → Set (EuclideanSpace ℝ (Fin n))} {hU : ∀ i, IsOpen (U i)}
    [∀ i, Nonempty (Piece U i)] {O : OverlapSystem (fun i => Piece U i)}
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)] {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (hrel : ∀ i j (x : Piece U i) (y : Piece U j),
      O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (h : HasLocalSourceModels U hU O e F V) (hV : IsOpen V)
    (hF : ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun z : V => F k z))
    {Y : Type*} [MetricSpace Y] {f : Quotient O.setoid → Y}
    (hf : Topology.IsOpenEmbedding f) {K : Set Y} (hK : IsCompact K) (hKV : K ⊆ f '' V)
    (o : ∀ i, Piece U i) {C : ℝ≥0}
    (hchart : ∀ i, LipschitzWith C (f ∘ O.include i))
    (hcenter : ∀ i, f (O.include i (o i)) ∈ K)
    {r₀ c : ℝ} (hr₀ : 0 < r₀) (hc : 0 < c)
    (hcompact : ∀ r : ℝ, 0 < r → r < r₀ → ∀ i, IsCompact (closedBall (o i) r))
    (hlower : ∀ k i y, y ∈ closedBall (o i) r₀ →
      c * dist y (o i) ≤ dist (e k i y) (e k i (o i)))
    (hconn : ∀ k i r, IsPreconnected (ball (e k i (o i)) r))
    (p : ∀ k, M k)
    (hnets : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ x : M k, |dist (p k) x - 1| ≤ δ → ∃ j ≤ N, dist x (e k j (o j)) < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
      {x : M k | |dist (p k) x - 1| ≤ δ} ⊆ F k '' V := by
  obtain ⟨a, ha, hinside⟩ := Poincare.Topology.exists_uniform_chart_radius_of_compact
    hf hV hK hKV O.include o hchart hcenter
  let r := min a (r₀ / 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hra : r ≤ a := min_le_left _ _
  have hrr₀ : r < r₀ := (min_le_right _ _).trans_lt (half_lt_self hr₀)
  have hballV (i : ℕ) : O.include i '' closedBall (o i) r ⊆ V :=
    (image_mono (closedBall_subset_closedBall hra)).trans (hinside i)
  obtain ⟨δ, hδ, N, hnet⟩ := hnets (c * r / 2) (by positivity)
  have hcover (i : ℕ) : ∀ᶠ k in atTop,
      ball (e k i (o i)) (c * r / 2) ⊆ (F k ∘ O.include i) '' ball (o i) r :=
    h.eventually_ball_subset_image hD hrel L he hV hF hr hc (hcompact r hr hrr₀ i)
      (hballV i) (fun k y hy => hlower k i y (closedBall_subset_closedBall hrr₀.le hy))
      (fun k => hconn k i _)
  have hfinite := (Finset.range (N + 1)).eventually_all.mpr fun i _ => hcover i
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hnet, hfinite] with k hknet hkcover x hx
  obtain ⟨i, hi, hxi⟩ := hknet x hx
  obtain ⟨y, hy, hxy⟩ := hkcover i (Finset.mem_range.mpr (by omega)) hxi
  exact ⟨O.include i y, hballV i (mem_image_of_mem _ (ball_subset_closedBall hy)), hxy⟩

end PoincareConjecture.ChartDistance
