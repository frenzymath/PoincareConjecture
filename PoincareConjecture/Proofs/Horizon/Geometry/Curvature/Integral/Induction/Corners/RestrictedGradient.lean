import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Fiber
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Projection
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
  [IsManifold (𝓡 (m + k)) ∞ M]

local instance restrictedGradient_ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem tangentNorm_gradient_openRegularFiberMetric_ge_half
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
    (hreg : ∀ y ∈ U, Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f y))
    (c : Fin k → ℝ) (g : RiemannianMetric (m + k) M)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (x : openFiber f U c)
    (w : Fin k → TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x))
    (wφ : TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x))
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1)))
    (hw : ∀ i, g.tangentNorm (openFiberIncl f U c x) (w i) ≤ 1)
    (hopposite : ∀ i, g.inner (openFiberIncl f U c x)
      (g.gradient (fun y => f y i) (openFiberIncl f U c x)) (w i) ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j → |g.inner (openFiberIncl f U c x)
      (g.gradient (fun y => f y i) (openFiberIncl f U c x))
      (g.gradient (fun y => f y j) (openFiberIncl f U c x))| ≤ δ)
    (hφw : g.tangentNorm (openFiberIncl f U c x) wφ ≤ 1)
    (hφopp : g.inner (openFiberIncl f U c x)
      (g.gradient φ (openFiberIncl f U c x)) wφ ≤ -1 + 2 * δ)
    (hφcross : ∀ i, |g.inner (openFiberIncl f U c x)
      (g.gradient φ (openFiberIncl f U c x))
      (g.gradient (fun y => f y i) (openFiberIncl f U c x))| ≤ δ) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    1 / 2 ≤ (openRegularFiberMetric hf U hreg c g).tangentNorm x
      ((openRegularFiberMetric hf U hreg c g).gradient (φ ∘ openFiberIncl f U c) x) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
    unfold TangentSpace
    infer_instance
  rw [tangentNorm_gradient_openRegularFiberMetric_eq_norm_starProjection hf U hreg c g hφ x]
  exact Poincare.CurvatureIntegral.norm_orthogonal_strainer_projection_ge_half
    (fun i => g.gradient (fun y => f y i) (openFiberIncl f U c x)) w
    (g.gradient φ (openFiberIncl f U c x)) wφ hδ (by simpa using hsmall)
    hw hopposite hcross hφw hφopp hφcross

theorem strainer_openFiber_gradient_ge_half
    (g : RiemannianMetric (m + k) M) (f : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i)) (U : Opens M)
    (w : ∀ y : M, Fin k → TangentSpace (𝓡 (m + k)) y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1)))
    (hw : ∀ y ∈ U, ∀ i, g.tangentNorm y (w y i) ≤ 1)
    (hopposite : ∀ y ∈ U, ∀ i, g.inner y (g.gradient (f i) y) (w y i) ≤ -1 + 2 * δ)
    (hcross : ∀ y ∈ U, ∀ i j, i ≠ j →
      |g.inner y (g.gradient (f i) y) (g.gradient (f j) y)| ≤ δ)
    (c : Fin k → ℝ) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (wφ : ∀ y : M, TangentSpace (𝓡 (m + k)) y)
    (hφw : ∀ y ∈ U, g.tangentNorm y (wφ y) ≤ 1)
    (hφopp : ∀ y ∈ U, g.inner y (g.gradient φ y) (wφ y) ≤ -1 + 2 * δ)
    (hφcross : ∀ y ∈ U, ∀ i, |g.inner y (g.gradient φ y) (g.gradient (f i) y)| ≤ δ) :
    let hb := Poincare.CurvatureIntegral.strainer_parameter_bounds k hδ hsmall
    let hreg := g.strainer_openFiber_regular f hf U w hδ hb.1 hb.2 hw hopposite hcross
    letI := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U hreg c
    letI := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c
    ∀ x : openFiber (fun y i => f i y) U c,
      1 / 2 ≤ (openRegularFiberMetric (contMDiff_pi_space.mpr hf) U hreg c g).tangentNorm x
        ((openRegularFiberMetric (contMDiff_pi_space.mpr hf) U hreg c g).gradient
          (φ ∘ openFiberIncl (fun y i => f i y) U c) x) := by
  dsimp only
  intro x
  exact tangentNorm_gradient_openRegularFiberMetric_ge_half
    (contMDiff_pi_space.mpr hf) U _ c g hφ x (w (openFiberIncl (fun y i => f i y) U c x))
    (wφ (openFiberIncl (fun y i => f i y) U c x)) hδ hsmall
    (hw _ (x : U).2) (hopposite _ (x : U).2) (hcross _ (x : U).2)
    (hφw _ (x : U).2) (hφopp _ (x : U).2) (hφcross _ (x : U).2)

end PoincareConjecture.RiemannianMetric
