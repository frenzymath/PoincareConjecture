import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.LocalModels










set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance



theorem HasLocalSourceModels.tendstoUniformlyOn_pairwise_distance
    {ι : Type*} {n : ℕ}
    {U : ι → Set (EuclideanSpace ℝ (Fin n))} {hU : ∀ i, IsOpen (U i)}
    [∀ i, Nonempty (Piece U i)]
    {O : OverlapSystem (fun i => Piece U i)}
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (hrel : ∀ i j (x : Piece U i) (y : Piece U j),
      O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    {F : ∀ k, Quotient O.setoid → M k} {V : Set (Quotient O.setoid)}
    (h : HasLocalSourceModels U hU O e F V) (hV : IsOpen V)
    {Y : Type*} [MetricSpace Y]
    (f : Quotient O.setoid → Y) (hf : Topology.IsOpenEmbedding f)
    (hreal : ∀ i j (x : Piece U i) (y : Piece U j),
      dist (f (O.include i x)) (f (O.include j y)) = D i j (x, y))
    {K : Set (Quotient O.setoid)} (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn
      (fun k (p : Quotient O.setoid × Quotient O.setoid) => dist (F k p.1) (F k p.2))
      (fun p => dist (f p.1) (f p.2)) atTop (K ×ˢ K) := by
  let : T2Space (Quotient O.setoid) := hf.isEmbedding.t2Space
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  obtain ⟨s, C, hC, hcover⟩ := exists_finite_compact_representatives O hK hK.isClosed
  have hCV (a : Σ i, Piece U i) (ha : a ∈ s) : O.include a.1 '' C a ⊆ V := by
    intro x hx
    apply hKV
    rw [← hcover]
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hx⟩⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have herror := s.eventually_all.mpr fun a ha => Metric.tendstoUniformlyOn_iff.mp
    (h.chart_approximation hD hrel L he hV a.1 (hC a ha) (hCV a ha))
      (ε / 3) (by positivity)
  have hdist := s.eventually_all.mpr fun a ha => s.eventually_all.mpr fun b hb =>
    eventually_dist_sub_limit_lt_on_compact hD (C a ×ˢ C b)
      ((hC a ha).prod (hC b hb)) (show 0 < ε / 3 by positivity)
  filter_upwards [herror, hdist] with k hkerror hkdist p hp
  obtain ⟨a, ha, x, hx, hpx⟩ := by
    simpa only [← hcover, mem_iUnion, exists_prop, mem_image] using hp.1
  obtain ⟨b, hb, y, hy, hpy⟩ := by
    simpa only [← hcover, mem_iUnion, exists_prop, mem_image] using hp.2
  have hnear (a : Σ i, Piece U i) (ha : a ∈ s) (x : Piece U a.1) (hx : x ∈ C a) :
      dist (F k (O.include a.1 x)) (e k a.1 x) < ε / 3 := by
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
      hkerror a ha x hx
  have hcross : dist (D a.1 b.1 (x, y)) (dist (e k a.1 x) (e k b.1 y)) < ε / 3 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hkdist a ha b hb (x, y) ⟨hx, hy⟩
  rw [← hpx, ← hpy, hreal]
  calc
    dist (D a.1 b.1 (x, y)) (dist (F k (O.include a.1 x)) (F k (O.include b.1 y))) ≤
        dist (D a.1 b.1 (x, y)) (dist (e k a.1 x) (e k b.1 y)) +
        dist (dist (e k a.1 x) (e k b.1 y))
          (dist (F k (O.include a.1 x)) (F k (O.include b.1 y))) := dist_triangle _ _ _
    _ ≤ dist (D a.1 b.1 (x, y)) (dist (e k a.1 x) (e k b.1 y)) +
        (dist (F k (O.include a.1 x)) (e k a.1 x) +
          dist (F k (O.include b.1 y)) (e k b.1 y)) := by
      gcongr
      simpa only [dist_comm] using dist_dist_dist_le
        (e k a.1 x) (e k b.1 y) (F k (O.include a.1 x)) (F k (O.include b.1 y))
    _ < ε := by linarith [hnear a ha x hx, hnear b hb y hy]

end PoincareConjecture.ChartDistance
