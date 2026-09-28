import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverCharts












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M28




theorem eventually_normalCover_jet_bound_of_curvature
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, ℝ → RiemannianMetric n (M k)} {p : ∀ k, M k}
    (D : ∀ k, LeviCivitaData (g k 0))
    {T' T r R ρ a b : ℝ} {N : ℕ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρR : ρ < R)
    (hcurv : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k 0).ball (p k) (r + R), (D k).curvatureDerivativeNorm l x ≤ C)
    (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ C : NormalChartCover (g k) (p k) T' T r R ρ a b N,
        C.HasMetricJetBound m B := by
  have hR : 0 < R := hρ.trans hρR
  choose B hB hbound using hcurv
  obtain ⟨C, hC, hjet⟩ := CoordinateExponential.exists_uniform_pullback_metric_jet_bound
    n m hρ hρR B hB
  refine ⟨C, hC, ?_⟩
  filter_upwards [(eventually_all_finite (Set.finite_Iic m)).mpr
    (fun l _ => hbound l)] with k hk
  let g₀ := g k 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M k → Type _) :=
    ⟨g₀.toRiemannianMetric⟩
  intro C i x hx
  obtain ⟨L, hL, hderiv⟩ := C.normalized i
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (C.chart i) (Metric.ball 0 R) := by
    simpa only [C.source] using (C.chart i).contMDiffOn
  have hnorm := g₀.pullbackCoefficients_zero_of_orthonormal (C.centre i)
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
    (C.map_zero i) hderiv hL
  apply hjet g₀ (D k) (C.chart i) he
  · intro y hy
    exact ⟨((C.chart i).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      ((C.source i).symm ▸ hy)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  · exact hnorm
  · exact CoordinateExponential.gauss_identity_of_radial_family g₀ he
      (C.radial_geodesic i) (fun v hv t ht =>
        g₀.tangentNorm_radial_of_normalized_exponential (C.centre i) L
          (C.map_zero i) hL hderiv (C.radial_geodesic i) hv ht)
  · intro l hl y hy
    apply hk l hl (C.chart i y)
    have hpoint : C.chart i y ∈ g₀.ball (C.centre i) R := by
      rw [← C.target]
      exact (C.chart i).map_source ((C.source i).symm ▸ hy)
    change g₀.edist (p k) (C.chart i y) < ENNReal.ofReal (r + R)
    rw [ENNReal.ofReal_add hr.le hR.le]
    exact Manifold.riemannianEDist_triangle.trans_lt
      (ENNReal.add_lt_add (C.centre_mem i) hpoint)
  · exact hx

end PoincareConjecture.M28
