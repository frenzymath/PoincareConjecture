import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AnnulusApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Family.CompactLimits










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_common_cone_realization_of_annular_distance_limits
    {n : ℕ} {M ι : Type*} {A : ι → Type*}
    [TopologicalSpace M] [T3Space M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [∀ i, MetricSpace (A i)] [∀ i, CompactSpace (A i)]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (Φ : ℕ → ∀ i, A i → M)
    (δ : ∀ i j, A i → A j → ℝ)
    (hradial : ∀ᶠ k in atTop, ∀ i (x : A i),
      a ≤ (g.edist p (Φ k i x)).toReal / L k ∧ (g.edist p (Φ k i x)).toReal / L k ≤ b)
    (hdiag : ∀ i, TendstoUniformly
      (fun k (z : A i × A i) => (g.edist (Φ k i z.1) (Φ k i z.2)).toReal / L k)
      (fun z => dist z.1 z.2) atTop)
    (hcross : ∀ i j x y, Tendsto
      (fun k => (g.edist (Φ k i x) (Φ k j y)).toReal / L k) atTop (𝓝 (δ i j x y))) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧ (∀ k, 0 < L (σ k)) ∧
      (∀ k i (x : A i), Φ (σ k) i x ∈ rescaledClosedAnnulus p (L (σ k)) a b) ∧
      ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
        ∃ ψ : ℕ → ∀ i, A i → asymptoticConeClosedAnnulus hcomparison a b,
        ∃ e : ∀ i, A i → asymptoticConeClosedAnnulus hcomparison a b,
          (∀ k i x, annulusConeRelation hcomparison (L (σ k))
            ((1 / ((k : ℝ) + 1)) / 4) (Φ (σ k) i x) (ψ k i x)) ∧
          (∀ k (x y : rescaledClosedAnnulus p (L (σ k)) a b)
            (z w : asymptoticConeClosedAnnulus hcomparison a b),
            annulusConeRelation hcomparison (L (σ k)) ((1 / ((k : ℝ) + 1)) / 4) x z →
            annulusConeRelation hcomparison (L (σ k)) ((1 / ((k : ℝ) + 1)) / 4) y w →
            |(g.edist (x : M) (y : M)).toReal / L (σ k) - dist z w| < 1 / ((k : ℝ) + 1)) ∧
          (∀ i, Isometry (e i)) ∧
          (∀ i, TendstoUniformly (fun k => ψ k i) (e i) (U : Filter ℕ)) ∧
          (∀ i j x y, dist (e i x) (e j y) = δ i j x y) ∧
          ∀ i z, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (ψ k i x) z < ε) → z ∈ range (e i) := by
  classical
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
  let B := asymptoticConeClosedAnnulus hcomparison a b
  let : CompactSpace B :=
    isCompact_iff_compactSpace.mp (isCompact_asymptoticConeClosedAnnulus hcomparison a b)
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose R hR happrox using fun k =>
    g.exists_annulusConeRelation_approximation_of_metricComplete D hc hsec p ha hab (hε k)
  have hchoose (k : ℕ) : ∃ j : ℕ, k ≤ j ∧ R k ≤ L j ∧
      ∀ i (x : A i), a ≤ (g.edist p (Φ j i x)).toReal / L j ∧
        (g.edist p (Φ j i x)).toReal / L j ≤ b :=
    ((eventually_ge_atTop k).and ((hL.eventually_ge_atTop (R k)).and hradial)).exists
  choose σ hσ hσR hσradial using hchoose
  have hσlim : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  have hexists (k : ℕ) (i : ι) (x : A i) : ∃ z : B,
      annulusConeRelation hcomparison (L (σ k)) (ε k / 4) (Φ (σ k) i x) z :=
    (happrox k (L (σ k)) (hσR k)).2.1 ⟨Φ (σ k) i x, hσradial k i x⟩
  choose ψ hψ using hexists
  have herror (k : ℕ) (i j : ι) (x : A i) (y : A j) :
      |(g.edist (Φ (σ k) i x) (Φ (σ k) j y)).toReal / L (σ k) -
        dist (ψ k i x) (ψ k j y)| < ε k :=
    (happrox k (L (σ k)) (hσR k)).2.2.2.2
      ⟨Φ (σ k) i x, hσradial k i x⟩ ⟨Φ (σ k) j y, hσradial k j y⟩
      (ψ k i x) (ψ k j y) (hψ k i x) (hψ k j y)
  have hdiagψ (i : ι) : TendstoUniformly
      (fun k (z : A i × A i) => dist (ψ k i z.1) (ψ k i z.2))
      (fun z => dist z.1 z.2) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    have hhalf : 0 < η / 2 := by positivity
    filter_upwards [hσlim.eventually (Metric.tendstoUniformly_iff.mp (hdiag i) (η / 2) hhalf),
      hεlim.eventually_lt_const hhalf] with k hk hεk z
    have he := herror k i i z.1 z.2
    have htriangle := dist_triangle (dist z.1 z.2)
      ((g.edist (Φ (σ k) i z.1) (Φ (σ k) i z.2)).toReal / L (σ k))
      (dist (ψ k i z.1) (ψ k i z.2))
    have hz := hk z
    simp only [Real.dist_eq] at htriangle hz ⊢
    linarith
  have hcrossψ (i j : ι) (x : A i) (y : A j) :
      Tendsto (fun k => dist (ψ k i x) (ψ k j y)) atTop (𝓝 (δ i j x y)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hhalf : 0 < η / 2 := by positivity
    filter_upwards [Metric.tendsto_nhds.mp ((hcross i j x y).comp hσlim) (η / 2) hhalf,
      hεlim.eventually_lt_const hhalf] with k hk hεk
    have he := herror k i j x y
    have htriangle := dist_triangle (dist (ψ k i x) (ψ k j y))
      ((g.edist (Φ (σ k) i x) (Φ (σ k) j y)).toReal / L (σ k)) (δ i j x y)
    rw [dist_comm (dist (ψ k i x) (ψ k j y))
      ((g.edist (Φ (σ k) i x) (Φ (σ k) j y)).toReal / L (σ k))] at htriangle
    simp only [Real.dist_eq, Function.comp_def] at htriangle hk ⊢
    linarith
  obtain ⟨U, hU, e, hisom, huniform, hcrossE, hcover⟩ :=
    exists_common_isometric_limits_preserving_cross_distances ψ δ hdiagψ hcrossψ
  exact ⟨σ, hσlim, (fun k => (hR k).trans_le (hσR k)), hσradial,
    U, hU, ψ, e, hψ, (fun k => (happrox k (L (σ k)) (hσR k)).2.2.2.2),
    hisom, huniform, hcrossE, hcover⟩

end PoincareConjecture.RiemannianMetric
