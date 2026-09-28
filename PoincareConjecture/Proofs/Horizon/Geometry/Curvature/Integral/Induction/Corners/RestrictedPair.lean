import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.RestrictedGradient










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle InnerProductSpace

universe u

namespace Poincare.CurvatureIntegral


theorem norm_starProjection_add_sq_le_of_opposite
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (z z' : E) {δ : ℝ}
    (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1)
    (hopp : ⟪z, z'⟫_ℝ ≤ -1 + 2 * δ) :
    ‖V.starProjection z + V.starProjection z'‖ ^ 2 ≤ 4 * δ := by
  rw [← map_add]
  have hproj := Submodule.norm_starProjection_apply_le V (z + z')
  have hsq : ‖V.starProjection (z + z')‖ ^ 2 ≤ ‖z + z'‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hproj 2
  have hzsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hz'sq : ‖z'‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z']
  rw [norm_add_sq_real] at hsq
  linarith

end Poincare.CurvatureIntegral

namespace PoincareConjecture.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
  [IsManifold (𝓡 (m + k)) ∞ M]

local instance restrictedPair_ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
  ⟨finrank_euclideanSpace_fin⟩



theorem tangentNorm_gradient_add_openRegularFiberMetric_sq_le
    {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
    (hreg : ∀ y ∈ U, Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f y))
    (c : Fin k → ℝ) (g : RiemannianMetric (m + k) M)
    {φ ψ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (hψ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ ψ)
    (x : openFiber f U c) {δ : ℝ}
    (hφunit : g.tangentNorm (openFiberIncl f U c x)
      (g.gradient φ (openFiberIncl f U c x)) ≤ 1)
    (hψunit : g.tangentNorm (openFiberIncl f U c x)
      (g.gradient ψ (openFiberIncl f U c x)) ≤ 1)
    (hpair : g.inner (openFiberIncl f U c x)
      (g.gradient φ (openFiberIncl f U c x))
      (g.gradient ψ (openFiberIncl f U c x)) ≤ -1 + 2 * δ) :
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let gL := openRegularFiberMetric hf U hreg c g
    gL.tangentNorm x (gL.gradient (φ ∘ openFiberIncl f U c) x +
      gL.gradient (ψ ∘ openFiberIncl f U c) x) ^ 2 ≤ 4 * δ := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + k)) (openFiberIncl f U c x)) := by
    unfold TangentSpace
    infer_instance
  dsimp only
  rw [openRegularFiberMetric_tangentNorm, map_add,
    mfderiv_gradient_openRegularFiberMetric hf U hreg c g hφ x,
    mfderiv_gradient_openRegularFiberMetric hf U hreg c g hψ x]
  exact Poincare.CurvatureIntegral.norm_starProjection_add_sq_le_of_opposite
    (Submodule.span ℝ (Set.range (fun i : Fin k =>
      g.gradient (fun y => f y i) (openFiberIncl f U c x))))ᗮ
    (g.gradient φ (openFiberIncl f U c x)) (g.gradient ψ (openFiberIncl f U c x))
    hφunit hψunit hpair



theorem strainer_openFiber_gradient_pair_bounds
    {m k : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    (f : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : TopologicalSpace.Opens M)
    (w : ∀ y : M, Fin k → TangentSpace (𝓡 (m + k)) y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1)))
    (hw : ∀ y ∈ U, ∀ i, g.tangentNorm y (w y i) ≤ 1)
    (hopposite : ∀ y ∈ U, ∀ i,
      g.inner y (g.gradient (f i) y) (w y i) ≤ -1 + 2 * δ)
    (hcross : ∀ y ∈ U, ∀ i j, i ≠ j →
      |g.inner y (g.gradient (f i) y) (g.gradient (f j) y)| ≤ δ)
    {φ ψ : M → ℝ}
    (hφ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (hψ : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ ψ)
    (hφunit : ∀ y ∈ U, g.tangentNorm y (g.gradient φ y) ≤ 1)
    (hψunit : ∀ y ∈ U, g.tangentNorm y (g.gradient ψ y) ≤ 1)
    (hpair : ∀ y ∈ U,
      g.inner y (g.gradient φ y) (g.gradient ψ y) ≤ -1 + 2 * δ)
    (hφcross : ∀ y ∈ U, ∀ i,
      |g.inner y (g.gradient φ y) (g.gradient (f i) y)| ≤ δ)
    (hψcross : ∀ y ∈ U, ∀ i,
      |g.inner y (g.gradient ψ y) (g.gradient (f i) y)| ≤ δ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∃ hreg : ∀ y ∈ U, Function.Surjective
        (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) (fun x i => f i x) y),
      ∀ c : Fin k → ℝ,
        letI := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U hreg c
        letI := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c
        let gL := PoincareConjecture.RiemannianMetric.openRegularFiberMetric
          (contMDiff_pi_space.mpr hf) U hreg c g
        ∀ x : openFiber (fun y i => f i y) U c,
          let vφ := gL.gradient (φ ∘ openFiberIncl (fun y i => f i y) U c) x
          let vψ := gL.gradient (ψ ∘ openFiberIncl (fun y i => f i y) U c) x
          (1 / 2 ≤ gL.tangentNorm x vφ ∧ gL.tangentNorm x vφ ≤ 1) ∧
          (1 / 2 ≤ gL.tangentNorm x vψ ∧ gL.tangentNorm x vψ ≤ 1) ∧
          gL.tangentNorm x (vφ + vψ) ^ 2 ≤ 4 * δ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hb := Poincare.CurvatureIntegral.strainer_parameter_bounds k hδ hsmall
  let hreg := g.strainer_openFiber_regular f hf U w hδ hb.1 hb.2 hw hopposite hcross
  refine ⟨hreg, ?_⟩
  intro c
  let := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U hreg c
  let := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c
  let gL := openRegularFiberMetric (contMDiff_pi_space.mpr hf) U hreg c g
  dsimp only
  intro x
  let p := openFiberIncl (fun y i => f i y) U c x
  have hp : p ∈ U := (x : U).2
  have hφlower := tangentNorm_gradient_openRegularFiberMetric_ge_half
    (contMDiff_pi_space.mpr hf) U hreg c g hφ x (w p) (g.gradient ψ p)
    hδ hsmall (hw p hp) (hopposite p hp) (hcross p hp)
    (hψunit p hp) (hpair p hp) (hφcross p hp)
  have hψpair : g.inner p (g.gradient ψ p) (g.gradient φ p) ≤ -1 + 2 * δ := by
    rw [g.symm]
    exact hpair p hp
  have hψlower := tangentNorm_gradient_openRegularFiberMetric_ge_half
    (contMDiff_pi_space.mpr hf) U hreg c g hψ x (w p) (g.gradient φ p)
    hδ hsmall (hw p hp) (hopposite p hp) (hcross p hp)
    (hφunit p hp) hψpair (hψcross p hp)
  have hφupper := tangentNorm_gradient_openRegularFiberMetric_le
    (contMDiff_pi_space.mpr hf) U hreg c g hφ x
  have hψupper := tangentNorm_gradient_openRegularFiberMetric_le
    (contMDiff_pi_space.mpr hf) U hreg c g hψ x
  exact ⟨⟨hφlower, hφupper.trans (hφunit p hp)⟩,
    ⟨hψlower, hψupper.trans (hψunit p hp)⟩,
    tangentNorm_gradient_add_openRegularFiberMetric_sq_le
      (contMDiff_pi_space.mpr hf) U hreg c g hφ hψ x
      (hφunit p hp) (hψunit p hp) (hpair p hp)⟩

end PoincareConjecture.RiemannianMetric
