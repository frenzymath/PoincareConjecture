import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Surface.SourceCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.LocalModels

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem HasLocalSourceModels.eventually_ball_subset_image
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
    (hF : ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun z : V => F k z))
    {i : ι} {x : Piece U i} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hcompact : IsCompact (closedBall x r))
    (hKV : O.include i '' closedBall x r ⊆ V)
    (hlower : ∀ k y, y ∈ closedBall x r → c * dist y x ≤ dist (e k i y) (e k i x))
    (hconn : ∀ k, IsPreconnected (ball (e k i x) (c * r / 2))) :
    ∀ᶠ k in atTop, ball (e k i x) (c * r / 2) ⊆
      (F k ∘ O.include i) '' ball x r := by
  have hcont : ∀ᶠ k in atTop, ContinuousOn (F k ∘ O.include i) (closedBall x r) := by
    filter_upwards [hF] with k hk
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hk.continuous.comp
      (((O.include_isOpenEmbedding i).continuous.comp continuous_subtype_val).subtype_mk
        (fun y : closedBall x r => hKV (mem_image_of_mem _ y.property)))
  have hopen : ∀ᶠ k in atTop, IsOpen ((F k ∘ O.include i) '' ball x r) := by
    filter_upwards [hF] with k hk
    let j : ball x r → V := fun y =>
      ⟨O.include i y, hKV (mem_image_of_mem _ (ball_subset_closedBall y.property))⟩
    have hj : IsOpenMap j :=
      ((O.include_isOpenEmbedding i).isOpenMap.domRestrict isOpen_ball).subtype_mk _
    have heq : range ((fun z : V => F k z) ∘ j) = (F k ∘ O.include i) '' ball x r := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.property, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [← heq]
    exact (hk.isOpenMap.comp hj).isOpen_range
  exact eventually_ball_subset_image_of_uniform_approximation hr hc hcompact hcont hopen
    hlower (h.chart_approximation hD hrel L he hV i hcompact hKV) hconn

end PoincareConjecture.ChartDistance
