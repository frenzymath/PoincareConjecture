import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceTransition










set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem eventually_mem_range_of_uniform_chart_approximation
    {Y : Type*} [MetricSpace Y] [LocallyCompactSpace Y]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e f : ∀ k, Y → M k} {L : ℝ≥0}
    (hL : ∀ k, LipschitzWith L (e k))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ k x y, c * dist x y ≤ dist (e k x) (e k y))
    (he : ∀ k, Topology.IsOpenEmbedding (e k))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {C : Set Y} (hC : IsCompact C)
    (happrox : TendstoUniformlyOn
      (fun k y => dist (f k y) (e k y)) (fun _ => 0) atTop C) :
    ∀ᶠ k in atTop, ∀ y ∈ C, f k y ∈ range (e k) := by
  have haux : ∀ᶠ k in atTop, ∀ y ∈ C, y ∈ C → f k y ∈ range (e k) := by
    refine hC.induction_on (p := fun S => ∀ᶠ k in atTop,
      ∀ y ∈ S, y ∈ C → f k y ∈ range (e k)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall (by simp)
    · intro S T hST hT
      exact hT.mono fun _ hk y hy => hk y (hST hy)
    · intro S T hS hT
      filter_upwards [hS, hT] with k hkS hkT y hy hyC
      exact hy.elim (fun h => hkS y h hyC) (fun h => hkT y h hyC)
    · intro x hx
      obtain ⟨r, hr, hball⟩ := exists_isCompact_closedBall x
      let δ := (c * r / 2) / ((L : ℝ) + 1)
      have hδ : 0 < δ := by dsimp [δ]; positivity
      refine ⟨ball x δ, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hδ)), ?_⟩
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp happrox (c * r / 2) (by positivity)]
        with k hk y hy hyC
      have hnear : dist (f k y) (e k y) < c * r / 2 := by
        simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using hk y hyC
      have hsmall : ((L : ℝ) + 1) * dist y x < c * r / 2 := by
        have h := (lt_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mp hy
        simpa only [mul_comm] using h
      have hdist : dist (f k y) (e k x) < c * r := by
        have htri := dist_triangle (f k y) (e k y) (e k x)
        have hupper := (hL k).dist_le_mul y x
        nlinarith [dist_nonneg (x := y) (y := x)]
      exact image_subset_range _ _
        (ball_subset_image_of_lower_bound (he k) hr hball
          (fun z => hlower k z x) (hconn k _ _) hc hdist)
  exact haux.mono fun _ hk y hy => hk y hy hy

end PoincareConjecture.ChartDistance
