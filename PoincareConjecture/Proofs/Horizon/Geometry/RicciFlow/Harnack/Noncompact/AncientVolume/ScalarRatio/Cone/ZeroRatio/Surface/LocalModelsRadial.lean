import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.LocalModels









set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance



theorem HasLocalSourceModels.tendstoUniformlyOn_basepoint_distance
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
    (p : ∀ k, M k) (ρ : Quotient O.setoid → ℝ)
    (hradial : ∀ i C, IsCompact C → O.include i '' C ⊆ V →
      TendstoUniformlyOn (fun k x => dist (p k) (e k i x))
        (fun x => ρ (O.include i x)) atTop C)
    {K : Set (Quotient O.setoid)} (hK : IsCompact K) (hKclosed : IsClosed K)
    (hKV : K ⊆ V) :
    TendstoUniformlyOn (fun k x => dist (p k) (F k x)) ρ atTop K := by
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  obtain ⟨s, C, hC, hcover⟩ := exists_finite_compact_representatives O hK hKclosed
  have hCV (a : Σ i, Piece U i) (ha : a ∈ s) : O.include a.1 '' C a ⊆ V := by
    intro x hx
    apply hKV
    rw [← hcover]
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hx⟩⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have herror := s.eventually_all.mpr fun a ha => Metric.tendstoUniformlyOn_iff.mp
    (h.chart_approximation hD hrel L he hV a.1 (hC a ha) (hCV a ha))
      (ε / 2) (by positivity)
  have hrad := s.eventually_all.mpr fun a ha => Metric.tendstoUniformlyOn_iff.mp
    (hradial a.1 (C a) (hC a ha) (hCV a ha)) (ε / 2) (by positivity)
  filter_upwards [herror, hrad] with k hkerror hkrad x hx
  obtain ⟨a, ha, y, hy, hxy⟩ := by
    simpa only [← hcover, mem_iUnion, exists_prop, mem_image] using hx
  rw [← hxy]
  have hnear : dist (F k (O.include a.1 y)) (e k a.1 y) < ε / 2 := by
    simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
      hkerror a ha y hy
  calc
    dist (ρ (O.include a.1 y)) (dist (p k) (F k (O.include a.1 y))) ≤
        dist (ρ (O.include a.1 y)) (dist (p k) (e k a.1 y)) +
        dist (dist (p k) (e k a.1 y)) (dist (p k) (F k (O.include a.1 y))) :=
      dist_triangle _ _ _
    _ ≤ dist (ρ (O.include a.1 y)) (dist (p k) (e k a.1 y)) +
        dist (F k (O.include a.1 y)) (e k a.1 y) := by
      gcongr
      simpa only [dist_self, zero_add, dist_comm] using
        dist_dist_dist_le (p k) (e k a.1 y) (p k) (F k (O.include a.1 y))
    _ < ε := by linarith [hkrad a ha y hy]

end PoincareConjecture.ChartDistance
