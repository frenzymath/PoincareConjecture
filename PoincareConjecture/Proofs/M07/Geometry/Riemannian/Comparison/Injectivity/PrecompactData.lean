import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Precompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_precompact_exponential_with_injectivity_data
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hcurv : ∀ x ∈ g.ball p R, D.curvatureTensorNorm x ≤ K) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let s := min R (Poincare.ODE.Jacobi.comparisonRadius K)
    ∃ L : E ≃L[ℝ] E, ∃ e : E → M,
      (∀ v w, g.pullbackCoefficients c.symm (c p) (L v) (L w) = inner ℝ v w) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      HasFDerivAt (fun v => c (e v)) L.toContinuousLinearMap 0 ∧
      (∀ v ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (e (t • v))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
          g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) ∧
      (∀ v ∈ Metric.ball 0 R, ∀ w : E,
        g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
          (mfderiv (𝓡 n) (𝓡 n) e v w) = inner ℝ v w) ∧
      (∀ v ∈ Metric.ball 0 s,
        Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e v) ∧
        ∀ w : E, ‖w‖ / 2 ≤ g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ∧
          g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) ≤ 3 * ‖w‖ / 2) ∧
      (∀ r : ℝ, 0 < r → 2 * r < s → ¬ InjOn e (Metric.closedBall 0 r) →
        ∃ v : E, 0 < ‖v‖ ∧ ‖v‖ ≤ r ∧ e ((2 : ℝ) • v) = p) ∧
      (∀ a b : E, g.pullbackCoefficients e 0 a b = inner ℝ a b) ∧
      ∀ r : ℝ, 0 < r → r ≤ R → MapsTo e (Metric.ball 0 r) (g.ball p r) := by
  dsimp only
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hb⟩ :=
    g.exists_precompact_exponential_with_differential_bounds D p hR hK hcompact hcurv
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))) he0 hed hL
  have hgauss := g.radial_gauss_identity D he hnorm (fun v hv => (hgeo v hv).1)
  let s := min R (Poincare.ODE.Jacobi.comparisonRadius K)
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hbounds (v) (hv : v ∈ Metric.ball 0 s) :=
    hb v (hsub hv) ((by simpa using hv : ‖v‖ < s).le.trans (min_le_right _ _))
  refine ⟨L, e, hL, he, he0, hed, hgeo, hgauss, hbounds, ?_, hnorm, ?_⟩
  · intro r hr hrs hnot
    obtain ⟨v, hvpos, hvr, hreturn⟩ := g.exists_returning_radial_vector_of_not_injOn
      hr hrs (he.mono hsub) (fun v hv => (hbounds v hv).1)
      (fun v hv => hgauss v (hsub hv))
      (fun v hv t ht => (hgeo v (hsub hv)).1 t (hsub ht)) hnot
    exact ⟨v, hvpos, hvr, hreturn.trans he0⟩
  · intro r hr hrR v hv
    have hvR := Metric.ball_subset_ball hrR hv
    have hdist := ((hgeo v hvR).2 1 (by simp)).2
    simp only [one_smul, ENNReal.ofReal_one, mul_one] at hdist
    exact hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by simpa using hv))

end PoincareConjecture.RiemannianMetric
