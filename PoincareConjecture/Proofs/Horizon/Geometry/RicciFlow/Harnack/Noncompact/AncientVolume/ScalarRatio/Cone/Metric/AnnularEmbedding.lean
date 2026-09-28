import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AnnulusApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.CompactLimit











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem exists_isometric_cone_limit_of_annular_distance_convergence
    {n : ℕ} {M A : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MetricSpace A] [CompactSpace A]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (Φ : ℕ → A → M)
    (hradial : ∀ᶠ k in atTop, ∀ x : A,
      a ≤ (g.edist p (Φ k x)).toReal / L k ∧ (g.edist p (Φ k x)).toReal / L k ≤ b)
    (hdist : TendstoUniformly
      (fun k => fun q : A × A => (g.edist (Φ k q.1) (Φ k q.2)).toReal / L k)
      (fun q => dist q.1 q.2) atTop) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧
      (∀ k, 0 < L (σ k)) ∧
      (∀ k x, Φ (σ k) x ∈ rescaledClosedAnnulus p (L (σ k)) a b) ∧
      ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
        ∃ ψ : ℕ → A → asymptoticConeClosedAnnulus hcomparison a b,
          ∃ e : A → asymptoticConeClosedAnnulus hcomparison a b,
            (∀ k x, annulusConeRelation hcomparison (L (σ k))
              ((1 / ((k : ℝ) + 1)) / 4) (Φ (σ k) x) (ψ k x)) ∧
            (∀ k (x y : rescaledClosedAnnulus p (L (σ k)) a b)
              (z w : asymptoticConeClosedAnnulus hcomparison a b),
              annulusConeRelation hcomparison (L (σ k)) ((1 / ((k : ℝ) + 1)) / 4) x z →
              annulusConeRelation hcomparison (L (σ k)) ((1 / ((k : ℝ) + 1)) / 4) y w →
              |(g.edist (x : M) (y : M)).toReal / L (σ k) - dist z w| <
                1 / ((k : ℝ) + 1)) ∧
            Isometry e ∧ TendstoUniformly ψ e (U : Filter ℕ) ∧
            ∀ z, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (ψ k x) z < ε) → z ∈ range e := by
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
      ∀ x : A, a ≤ (g.edist p (Φ j x)).toReal / L j ∧
        (g.edist p (Φ j x)).toReal / L j ≤ b :=
    ((eventually_ge_atTop k).and ((hL.eventually_ge_atTop (R k)).and hradial)).exists
  choose σ hσ hσR hσradial using hchoose
  have hσlim : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  have hexists (k : ℕ) (x : A) : ∃ z : B,
      annulusConeRelation hcomparison (L (σ k)) (ε k / 4) (Φ (σ k) x) z :=
    (happrox k (L (σ k)) (hσR k)).2.1 ⟨Φ (σ k) x, hσradial k x⟩
  choose ψ hψ using hexists
  have hdistortion (k : ℕ) (x y : A) :
      |(g.edist (Φ (σ k) x) (Φ (σ k) y)).toReal / L (σ k) - dist (ψ k x) (ψ k y)| <
        ε k :=
    (happrox k (L (σ k)) (hσR k)).2.2.2.2
      ⟨Φ (σ k) x, hσradial k x⟩ ⟨Φ (σ k) y, hσradial k y⟩
      (ψ k x) (ψ k y) (hψ k x) (hψ k y)
  have hψdist : TendstoUniformly
      (fun k => fun q : A × A => dist (ψ k q.1) (ψ k q.2))
      (fun q => dist q.1 q.2) atTop := by
    rw [Metric.tendstoUniformly_iff] at hdist ⊢
    intro δ hδ
    have hhalf : 0 < δ / 2 := by positivity
    filter_upwards [hσlim.eventually (hdist (δ / 2) hhalf),
      hεlim.eventually_lt_const hhalf] with k hk hεk q
    have herror := hdistortion k q.1 q.2
    change dist (dist q.1 q.2) (dist (ψ k q.1) (ψ k q.2)) < δ
    calc
      _ ≤ dist (dist q.1 q.2)
          ((g.edist (Φ (σ k) q.1) (Φ (σ k) q.2)).toReal / L (σ k)) +
          dist ((g.edist (Φ (σ k) q.1) (Φ (σ k) q.2)).toReal / L (σ k))
            (dist (ψ k q.1) (ψ k q.2)) := dist_triangle _ _ _
      _ < δ := by
        have hq := hk q
        simp only [Real.dist_eq] at hq ⊢
        linarith
  obtain ⟨U, hU, e, he, hlim, hcover⟩ :=
    exists_isometric_limit_covering_approximated_points ψ hψdist
  exact ⟨σ, hσlim, (fun k => (hR k).trans_le (hσR k)), hσradial,
    U, hU, ψ, e, hψ, (fun k => (happrox k (L (σ k)) (hσR k)).2.2.2.2),
    he, hlim, hcover⟩

end PoincareConjecture.RiemannianMetric
