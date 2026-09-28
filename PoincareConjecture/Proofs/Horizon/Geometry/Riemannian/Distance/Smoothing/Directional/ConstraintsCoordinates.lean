import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Coordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution.DirectionalLocal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology Bundle NNReal

namespace PoincareConjecture.LeviCivitaData
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem norm_fderiv_parametrization_le_of_gradient_norm_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {z : EuclideanSpace ℝ (Fin n)}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e z)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e z))
    {N A : ℝ} (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hgrad : g.tangentNorm (e z) (D.gradient f (e z)) ≤ N)
    (hmetric : ∀ w : EuclideanSpace ℝ (Fin n),
      g.pullbackCoefficients e z w w ≤ A * ‖w‖ ^ 2) :
    ‖fderiv ℝ (f ∘ e) z‖ ≤ N * A := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hnorm (w : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z w) ≤ A * ‖w‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hA0 (norm_nonneg _), ?_⟩
    have hb : g.inner (e z) (mfderiv (𝓡 n) (𝓡 n) e z w)
        (mfderiv (𝓡 n) (𝓡 n) e z w) ≤ A * ‖w‖ ^ 2 := by
      simpa only [RiemannianMetric.pullbackCoefficients,
        ContinuousLinearMap.bilinearComp_apply] using! hmetric w
    have hAA : A ≤ A ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg ‖w‖)]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hN hA0)
  intro w
  have heq := congrArg (fun T => T w)
    (mfderiv_comp z (hf.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at heq
  change fderiv ℝ (f ∘ e) z w =
    mvfderiv (𝓡 n) f (e z) (mfderiv (𝓡 n) (𝓡 n) e z w) at heq
  rw [Real.norm_eq_abs, heq]
  exact (D.abs_mvfderiv_le_gradient_norm _ _ _).trans (by
    calc
      _ ≤ N * g.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z w) :=
        mul_le_mul_of_nonneg_right hgrad (Real.sqrt_nonneg _)
      _ ≤ N * (A * ‖w‖) := mul_le_mul_of_nonneg_left (hnorm w) hN
      _ = _ := by ring)

theorem directional_upper_support_in_parametrization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {z : EuclideanSpace ℝ (Fin n)}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e z)
    {d q : M → ℝ} (hq : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ q (e z))
    (htouch : q (e z) = d (e z)) (hmajor : ∀ᶠ y in 𝓝 (e z), d y ≤ q y)
    {N A : ℝ} (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hgrad : g.tangentNorm (e z) (D.gradient q (e z)) ≤ N)
    (hmetric : ∀ w : EuclideanSpace ℝ (Fin n),
      g.pullbackCoefficients e z w w ≤ A * ‖w‖ ^ 2)
    {v : EuclideanSpace ℝ (Fin n)} {B : ℝ}
    (hdir : |mvfderiv (𝓡 n) q (e z) (mfderiv (𝓡 n) (𝓡 n) e z v)| ≤ B) :
    DifferentiableAt ℝ (q ∘ e) z ∧ (q ∘ e) z = (d ∘ e) z ∧
      (∀ᶠ y in 𝓝 z, (d ∘ e) y ≤ (q ∘ e) y) ∧
      ‖fderiv ℝ (q ∘ e) z‖ ≤ N * A ∧ |fderiv ℝ (q ∘ e) z v| ≤ B := by
  refine ⟨(contMDiffAt_iff_contDiffAt.mp (hq.comp z he)).differentiableAt (by simp),
    htouch, he.continuousAt.tendsto.eventually hmajor,
    D.norm_fderiv_parametrization_le_of_gradient_norm_le e he hq hN hA hgrad hmetric, ?_⟩
  have heq := congrArg (fun T => T v)
    (mfderiv_comp z (hq.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at heq
  change fderiv ℝ (q ∘ e) z v =
    mvfderiv (𝓡 n) q (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) at heq
  simpa only [heq] using hdir

theorem exists_contMDiff_directional_approx_in_parametrization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x₀ : EuclideanSpace ℝ (Fin n)} {r R : ℝ} (hrR : r < R)
    (hsource : Metric.ball x₀ R ⊆ e.source) {d : M → ℝ} {K : ℝ≥0}
    (hd : LipschitzOnWith K (d ∘ e) (Metric.ball x₀ R))
    {b C G : ℝ} (hb : 0 < b) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R)
      (fun z => d (e z) - C * ‖z‖ ^ 2 / 2))
    (hmetric : ∀ z ∈ Metric.ball x₀ r, ∀ v : EuclideanSpace ℝ (Fin n),
      b * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e z v v)
    (hconn : ∀ z ∈ Metric.ball x₀ r,
      ‖CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) z‖ ≤ G)
    {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (lo hi : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsupport : ∀ i x, x ∈ Metric.ball x₀ r → ∀ y ∈ Metric.ball x₀ R,
      ∃ q : EuclideanSpace ℝ (Fin n) → ℝ,
        DifferentiableAt ℝ q y ∧ q y = d (e y) ∧
        (∀ᶠ z in 𝓝 y, d (e z) ≤ q z) ∧
        lo i x ≤ fderiv ℝ q y (v i x) ∧ fderiv ℝ q y (v i x) ≤ hi i x)
    {ε : ℝ} (hε : 0 < ε) :
    let U := e.target ∩ e.symm ⁻¹' Metric.ball x₀ r
    ∃ rho : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      (∀ y ∈ U, |rho y - d y| ≤ ε) ∧
      (∀ y ∈ U, g.tangentNorm y (D.gradient rho y) ≤ (K : ℝ) / Real.sqrt b) ∧
      (∀ y ∈ U, ∀ w : TangentSpace (𝓡 n) y,
        D.hessian rho y w w ≤ ((C + (K : ℝ) * G) / b) * g.inner y w w) ∧
      ∀ i z, z ∈ Metric.ball x₀ r →
        lo i z ≤ mvfderiv (𝓡 n) rho (e z) (mfderiv (𝓡 n) (𝓡 n) e z (v i z)) ∧
          mvfderiv (𝓡 n) rho (e z) (mfderiv (𝓡 n) (𝓡 n) e z (v i z)) ≤ hi i z := by
  dsimp only
  let U := e.target ∩ e.symm ⁻¹' Metric.ball x₀ r
  have hU : IsOpen U := hei.continuousOn.isOpen_inter_preimage e.open_target Metric.isOpen_ball
  have hsmall : Metric.ball x₀ r ⊆ e.source :=
    (Metric.ball_subset_ball hrR.le).trans hsource
  obtain ⟨u, hu, hLip, herr, hess, hdir⟩ :=
    Poincare.exists_contDiff_hessian_directional_approx_of_upper_support
      hrR hd hconc v lo hi hsupport hε
  let rho := u ∘ e.symm
  have hrho : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U := by
    intro y hy
    exact ((contMDiffAt_iff_contDiffAt.mpr hu.contDiffAt).comp y
      (hei.contMDiffAt (e.open_target.mem_nhds hy.1))).contMDiffWithinAt
  have hparam (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ e.source) :
      (rho ∘ e) =ᶠ[𝓝 z] u := by
    filter_upwards [e.open_source.mem_nhds hz] with w hw
    exact congrArg u (e.left_inv hw)
  have heU (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball x₀ r) :
      e z ∈ U := ⟨e.map_source (hsmall hz), by
        simpa only [mem_preimage, e.left_inv (hsmall hz)] using hz⟩
  have hbounds (y : M) (hy : y ∈ U) :
      g.tangentNorm y (D.gradient rho y) ≤ (K : ℝ) / Real.sqrt b ∧
      ∀ w : TangentSpace (𝓡 n) y,
        D.hessian rho y w w ≤ ((C + (K : ℝ) * G) / b) * g.inner y w w := by
    let z := e.symm y
    have hz : z ∈ e.source := e.map_target hy.1
    have heq := hparam z hz
    have hfirst : ‖fderiv ℝ (rho ∘ e) z‖ ≤ (K : ℝ) := by
      rw [heq.fderiv_eq]
      exact norm_fderiv_le_of_lipschitz ℝ hLip
    have hsecond : ∀ w : EuclideanSpace ℝ (Fin n),
        fderiv ℝ (fderiv ℝ (rho ∘ e)) z w w ≤ C * ‖w‖ ^ 2 := by
      rw [heq.fderiv.fderiv_eq]
      exact hess z hy.2
    have hconverted := D.intrinsic_bounds_of_parametrization e he hei hz
      (hrho.contMDiffAt (hU.mem_nhds (heU z hy.2))) hb hC K.coe_nonneg hG
      (hmetric z hy.2) hfirst hsecond (hconn z hy.2)
    let P : M → Prop := fun y =>
      g.tangentNorm y (D.gradient rho y) ≤ (K : ℝ) / Real.sqrt b ∧
      ∀ w : TangentSpace (𝓡 n) y,
        D.hessian rho y w w ≤ ((C + (K : ℝ) * G) / b) * g.inner y w w
    exact (congrArg P (e.right_inv hy.1)).mp hconverted
  refine ⟨rho, hrho, ?_, fun y hy => (hbounds y hy).1,
    fun y hy => (hbounds y hy).2, ?_⟩
  · intro y hy
    have hbnd := herr (e.symm y) (Metric.ball_subset_ball hrR.le hy.2)
    simpa only [Real.dist_eq, rho, Function.comp_apply, e.right_inv hy.1] using hbnd
  · intro i z hz
    have hez := he.contMDiffAt (e.open_source.mem_nhds (hsmall hz))
    have hrhoz := hrho.contMDiffAt (hU.mem_nhds (heU z hz))
    have heq := congrArg (fun T => T (v i z))
      (mfderiv_comp z (hrhoz.mdifferentiableAt (by simp)) (hez.mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change fderiv ℝ (rho ∘ e) z (v i z) =
      mvfderiv (𝓡 n) rho (e z) (mfderiv (𝓡 n) (𝓡 n) e z (v i z)) at heq
    rw [(hparam z (hsmall hz)).fderiv_eq] at heq
    simpa only [← heq] using hdir i z hz

end PoincareConjecture.LeviCivitaData
