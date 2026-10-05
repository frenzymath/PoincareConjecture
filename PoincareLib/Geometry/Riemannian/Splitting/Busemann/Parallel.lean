import PoincareLib.Geometry.Riemannian.Splitting.Busemann.Calibration
import PoincareLib.Geometry.Riemannian.Splitting.Busemann.GradientBound
import PoincareLib.Geometry.Riemannian.Splitting.Busemann.Bochner

/-!
# Parallel gradients of harmonic Busemann functions

Completeness constructs calibrated points on every sphere. These give the
unit-gradient identity once smoothness is known; harmonicity and nonnegative
Ricci curvature then give a parallel gradient and vanishing Hessian.

These are the last steps of Morgan--Tian, Proposition 2.3, pp. 21--23,
and the proof of Lemma 2.14, pp. 28--29. The analytic production of smooth
harmonicity is a separate obligation, not a conclusion of this module.
-/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] (g : RiemannianMetric n M)

/-- Smooth Busemann functions have unit gradient, by calibrated spheres. -/
theorem busemann_gradient_normSq_eq_one (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ)) (x : M) :
    g.inner x (D.gradient (g.busemann γ) x) (D.gradient (g.busemann γ) x) = 1 := by
  apply D.gradient_normSq_eq_one_of_distance_lipschitz_of_calibrated_spheres
    hsmooth (g.abs_busemann_sub_le hγ)
  exact fun r hr => g.exists_busemann_calibrated_point hcomplete hγ x hr

/-- The gradient of a smooth harmonic Busemann function is parallel. -/
theorem busemann_connection_gradient_eq_zero (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ))
    (hharm : ∀ x, D.laplacian (g.busemann γ) x = 0)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    D.connection (D.gradient (g.busemann γ)) x v = 0 :=
  D.connection_gradient_eq_zero_of_harmonic_of_constant_normSq hsmooth hRic hharm
    (g.busemann_gradient_normSq_eq_one D hcomplete hγ hsmooth) x v

/-- The retained Hessian of a smooth harmonic Busemann function vanishes. -/
theorem busemann_hessian_eq_zero (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.busemann γ))
    (hharm : ∀ x, D.laplacian (g.busemann γ) x = 0)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (g.busemann γ) x v w = 0 :=
  D.hessian_eq_zero_of_harmonic_of_constant_normSq hsmooth hRic hharm
    (g.busemann_gradient_normSq_eq_one D hcomplete hγ hsmooth) x v w

end PoincareMT.RiemannianMetric
