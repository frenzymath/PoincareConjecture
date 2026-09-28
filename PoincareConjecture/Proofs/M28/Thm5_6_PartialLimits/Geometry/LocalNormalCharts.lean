import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Ellipticity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M28

theorem riemannian_ball_subset_of_margin
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {p q : M} {r s S : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hq : q ∈ g.ball p r) (hmargin : r + s ≤ S) :
    g.ball q s ⊆ g.ball p S := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x hx
  change g.edist p x < ENNReal.ofReal S
  have hsum : ENNReal.ofReal r + ENNReal.ofReal s ≤ ENNReal.ofReal S := by
    rw [← ENNReal.ofReal_add hr hs]
    exact ENNReal.ofReal_le_ofReal hmargin
  exact (Manifold.riemannianEDist_triangle.trans_lt (ENNReal.add_lt_add hq hx)).trans_le hsum

theorem exists_normal_chart_of_local_noncollapse
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {K δ v r S R ρ : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hv : 0 < v) (hr : 0 < r) (hmargin : r + 2 * δ ≤ S)
    (hRdef : R = RiemannianMetric.localInjectivityRadius n K δ v)
    (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) ≤ 3)
    (hcompact : IsCompact (closure (g.ball p S)))
    (hcurv : ∀ x ∈ g.ball p S, D.curvatureTensorNorm x ≤ K)
    (hvol : ∀ q ∈ g.ball p r, ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q δ))
    (q : M) (hq : q ∈ g.ball p r) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      Φ.source = Metric.ball 0 R ∧ Φ.target = g.ball q R ∧ Φ 0 = q ∧
      (∀ u w, g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
        (extChartAt (𝓡 n) q q) (L u) (L w) = inner ℝ u w) ∧
      HasFDerivAt (fun w => extChartAt (𝓡 n) q (Φ w)) L.toContinuousLinearMap 0 ∧
      (∀ w ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
      (∀ w ∈ Metric.ball 0 R, g.edist q (Φ w) = ENNReal.ofReal ‖w‖) ∧
      ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ w,
        (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients Φ x w w ∧
          g.pullbackCoefficients Φ x w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2 := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsub := riemannian_ball_subset_of_margin g hr.le
    (by positivity : 0 ≤ 2 * δ) hq hmargin
  have hcompactq : IsCompact (closure (g.ball q (2 * δ))) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hsub)
  obtain ⟨hR, hRδ, L, Φ, hsource, htarget, hzero, hL, hderiv, hgeoδ, hdist⟩ :=
    g.exists_uniform_precompact_exponential_diffeomorph D q hn hK hδ hv
      hcompactq (fun x hx => hcurv x (hsub hx)) (hvol q hq)
  rw [← hRdef] at hR hRδ hsource htarget hdist
  have hgeo : ∀ w ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R} :=
    fun w hw t ht => hgeoδ w (Metric.ball_subset_ball hRδ.le hw) t
      (Metric.ball_subset_ball hRδ.le ht)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 R) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal q
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
    hzero hderiv hL
  have hradial (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ Metric.ball 0 R) :
      g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (Φ (t • w))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => Φ (s • w)) t 1) = ‖w‖ ∧
          g.edist q (Φ (t • w)) ≤ ENNReal.ofReal ‖w‖ * ENNReal.ofReal t := by
    refine ⟨hgeo w hw, ?_⟩
    intro t ht
    refine ⟨g.tangentNorm_radial_of_normalized_exponential q L
      hzero hL hderiv hgeo hw ht, ?_⟩
    have htw : t • w ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)).trans_lt
        (by simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hw)
    rw [hdist _ htw, norm_smul, Real.norm_of_nonneg ht.1, ENNReal.ofReal_mul ht.1, mul_comm]
  have hbound := g.radial_exponential_uniform_bounds D hρR hsmall he hnorm hradial
    (fun x hx => hcurv x (hsub (hx.trans_le
      (ENNReal.ofReal_le_ofReal (by linarith : R ≤ 2 * δ)))))
  exact ⟨L, Φ, hsource, htarget, hzero, hL, hderiv, hgeo, hdist,
    fun x hx w => ((hbound x hx).2 w).2⟩

end PoincareConjecture.M28
