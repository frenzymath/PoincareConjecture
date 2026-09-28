import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture
namespace DeepHorn

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem rescaledMetric_laplacian (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    (rescaledMetric_connection g D c hc).laplacian f x = c⁻¹ * D.laplacian f x := by
  let A := D.connection (D.gradient f) x
  let B : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v w => g.inner x (A v) w)
      (by intros; simp)
      (by intros; simp)
      (by intros; simp)
      (by intros; simp)
  have h := rescaledMetric_bilinear_trace g c hc x B
  change (∑ i, D.hessian f x ((rescaledMetric g c hc).orthonormalBasis x i)
      ((rescaledMetric g c hc).orthonormalBasis x i)) =
    c⁻¹ * ∑ i, D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  simpa only [B, A, LinearMap.mk₂_apply, D.hessian_eq_inner_connection_gradient hf] using h

theorem rescaledMetric_scalar_laplacian (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M) :
    (rescaledMetric_connection g D c hc).laplacian
        (rescaledMetric_connection g D c hc).scalarCurvature x =
      c⁻¹ ^ 2 * D.laplacian D.scalarCurvature x := by
  have heq : (rescaledMetric_connection g D c hc).scalarCurvature =
      fun y => c⁻¹ * D.scalarCurvature y := funext (rescaledMetric_scalarCurvature g D c hc)
  rw [heq, LeviCivitaData.laplacian_const_mul,
    rescaledMetric_laplacian D c hc (D.contMDiff_scalarCurvature x)]
  ring

theorem scalar_laplacian_eq_of_local_isometry
    {M' : Type*} [TopologicalSpace M']
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M'] [IsManifold (𝓡 n) ∞ M']
    {g' : RiemannianMetric n M'} (D : LeviCivitaData g) (D' : LeviCivitaData g')
    {f : M → M'} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y,
      g.inner y v w = g'.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v)
        (mfderiv (𝓡 n) (𝓡 n) f y w)) {x : M} (hx : x ∈ U) :
    D.laplacian D.scalarCurvature x = D'.laplacian D'.scalarCurvature (f x) := by
  have hscalar : D.scalarCurvature =ᶠ[𝓝 x] D'.scalarCurvature ∘ f :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
      (fun y hy => D.scalarCurvature_eq_of_local_isometry D' hU hf hmetric hy)
  rw [D.laplacian_eq_of_eventuallyEq hscalar]
  apply D.laplacian_comp_of_metric_pullback D'
    ((hf x hx).contMDiffAt (hU.mem_nhds hx))
  · filter_upwards [hU.mem_nhds hx] with y hy
    have hb := g.mfderiv_bijective_of_pullback_eq g' y
      (fun v w => (hmetric y hy v w).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) := by
      unfold TangentSpace
      infer_instance
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f y)) := by
      unfold TangentSpace
      infer_instance
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 n) (𝓡 n) f y).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  · exact Filter.eventually_of_mem (hU.mem_nhds hx) hmetric
  · exact D'.contMDiff_scalarCurvature (f x)

end DeepHorn

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem normalized_realization_scalar_laplacian
    (N : EpsilonNeck g) (D' : LeviCivitaData g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) :
    D.laplacian D.scalarCurvature 0 =
      N.scale ^ 4 * D'.laplacian D'.scalarCurvature (N.coordinate_map (q, s)) := by
  let F := N.centeredEuclideanParametrization q s
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add (RiemannianMetric.lineModelEquiv 2).symm.continuous))
  have h0U : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hs
  obtain ⟨V, hV, hVo, h0V⟩ := mem_nhds_iff.mp (heq.and (hU.mem_nhds h0U))
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F V := fun x hx =>
    (N.centeredEuclideanParametrization_contMDiffAt q s (hV hx).2).contMDiffWithinAt
  have hc : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let DN := rescaledMetric_connection g D' (N.scale⁻¹ ^ 2) hc
  have hmetric : ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner x v w = (rescaledMetric g (N.scale⁻¹ ^ 2) hc).inner (F x)
        (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w) := by
    intro x hx v w
    change h.euclideanCoefficients x v w = _
    rw [(hV hx).1, N.normalizedEuclideanCoefficients_eq_pullback q s (hV hx).2,
      rescaledMetric_inner]
  have htransport := DeepHorn.scalar_laplacian_eq_of_local_isometry D DN hVo hF hmetric h0V
  simpa only [DN, DeepHorn.rescaledMetric_scalar_laplacian, inv_pow, inv_inv,
    ← pow_mul, F, centeredEuclideanParametrization_zero] using htransport



theorem scalar_evolution_margin_of_normalized_laplacian
    (N : EpsilonNeck g) (D' : LeviCivitaData g) (q : UnitTwoSphere)
    (hcenter : N.coordinate_map (q, 0) = N.center)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q 0)
    (hlap : -(1 / 6 : ℝ) ≤ D.laplacian D.scalarCurvature 0) :
    (1 / 2 : ℝ) * D'.scalarCurvature N.center ^ 2 ≤
      D'.laplacian D'.scalarCurvature N.center + 2 * D'.ricciNormSq N.center := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have htransport := N.normalized_realization_scalar_laplacian D' q hzero D heq
  rw [hcenter] at htransport
  have hnormal := N.scale_sq_mul_scalar_center_of_connection D'
  have hfour : N.scale ^ 4 * D'.scalarCurvature N.center ^ 2 = 1 := by
    nlinarith [sq_nonneg (N.scale ^ 2 * D'.scalarCurvature N.center - 1),
      congrArg (fun r : ℝ => r ^ 2) hnormal]
  have hpositive : 0 < N.scale ^ 4 := pow_pos N.scale_pos _
  have hbound : -(1 / 6 : ℝ) * D'.scalarCurvature N.center ^ 2 ≤
      D'.laplacian D'.scalarCurvature N.center := by
    apply (mul_le_mul_iff_right₀ hpositive).mp
    nlinarith [hlap, htransport, hfour]
  have htrace := D'.scalarCurvature_sq_le N.center
  norm_num at htrace
  linarith

end EpsilonNeck

namespace RicciFlow

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem scalar_time_derivative_margin_of_normalized_laplacian
    (hM04 : RicciFlowCurvatureTheory.{u}) {J : Set ℝ}
    (F : RicciFlow 3 M J) {t : ℝ} (ht : t ∈ J)
    (N : EpsilonNeck (F.metric t)) (q : UnitTwoSphere)
    (hcenter : N.coordinate_map (q, 0) = N.center)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q 0)
    (hlap : -(1 / 6 : ℝ) ≤ D.laplacian D.scalarCurvature 0) :
    ∃ d : ℝ, HasDerivWithinAt (fun s => (F.connection s).scalarCurvature N.center) d J t ∧
      (1 / 2 : ℝ) * (F.connection t).scalarCurvature N.center ^ 2 ≤ d := by
  exact ⟨_, hM04.scalar_evolution 3 M J F t ht N.center,
    N.scalar_evolution_margin_of_normalized_laplacian (F.connection t) q hcenter D heq hlap⟩

end RicciFlow
end PoincareConjecture
