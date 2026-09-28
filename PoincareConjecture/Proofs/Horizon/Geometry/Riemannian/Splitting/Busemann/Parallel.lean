import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.GradientBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Bochner












noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] (g : RiemannianMetric n M)


theorem busemann_gradient_normSq_eq_one (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ)) (x : M) :
    g.inner x (D.gradient (g.busemann γ) x) (D.gradient (g.busemann γ) x) = 1 := by
  apply D.gradient_normSq_eq_one_of_distance_lipschitz_of_calibrated_spheres
    hsmooth (g.abs_busemann_sub_le hγ)
  exact fun r hr => g.exists_busemann_calibrated_point hcomplete hγ x hr


theorem busemann_connection_gradient_eq_zero (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ))
    (hharm : ∀ x, D.laplacian (g.busemann γ) x = 0)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    D.connection (D.gradient (g.busemann γ)) x v = 0 :=
  D.connection_gradient_eq_zero_of_harmonic_of_constant_normSq hsmooth hRic hharm
    (g.busemann_gradient_normSq_eq_one D hcomplete hγ hsmooth) x v


theorem busemann_hessian_eq_zero (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ))
    (hharm : ∀ x, D.laplacian (g.busemann γ) x = 0)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (g.busemann γ) x v w = 0 :=
  D.hessian_eq_zero_of_harmonic_of_constant_normSq hsmooth hRic hharm
    (g.busemann_gradient_normSq_eq_one D hcomplete hγ hsmooth) x v w

end PoincareConjecture.RiemannianMetric
