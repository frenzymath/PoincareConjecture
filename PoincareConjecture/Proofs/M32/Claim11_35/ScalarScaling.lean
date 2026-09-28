import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M32

section Scaling

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem scaledLeviCivita_gradient (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    (u : M → ℝ) (x : M) :
    (M13.scaleLeviCivitaData D Q hQ).gradient u x = Q⁻¹ • D.gradient u x := by
  apply (g.inner_isInvertible x).injective
  ext v
  have h := (M13.scaleLeviCivitaData D Q hQ).inner_gradient u x v
  change Q * g.inner x ((M13.scaleLeviCivitaData D Q hQ).gradient u x) v =
    mvfderiv (𝓡 n) u x v at h
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
  field_simp [hQ.ne'] at h ⊢
  nlinarith

theorem scaledLeviCivita_laplacian (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    {u : M → ℝ} {x : M} (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u x) :
    (M13.scaleLeviCivitaData D Q hQ).laplacian u x = D.laplacian u x / Q := by
  have hgrad : (M13.scaleLeviCivitaData D Q hQ).gradient u = Q⁻¹ • D.gradient u := by
    funext y
    exact scaledLeviCivita_gradient D hQ u y
  rw [(M13.scaleLeviCivitaData D Q hQ).laplacian_eq_trace_connection_gradient hu,
    D.laplacian_eq_trace_connection_gradient hu, hgrad]
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (D.connection (Q⁻¹ • D.gradient u) x).toLinearMap = _
  rw [D.connection.isCovariantDerivativeOn.smul_const Q⁻¹
    ((D.contMDiffAt_gradient hu).mdifferentiableAt (by simp))]
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (Q⁻¹ • (D.connection (D.gradient u) x).toLinearMap) = _
  simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]

end Scaling

section LocalHomothety

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem scalarCurvature_eq_of_local_homothety [T2Space N]
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    {x : M} (hx : x ∈ U) :
    D.scalarCurvature x = D'.scalarCurvature (f x) / Q := by
  have hlocal := D.scalarCurvature_eq_of_local_isometry
    (M13.scaleLeviCivitaData D' Q hQ) hU hf hmetric hx
  exact hlocal.trans (M13.homothety_scalarCurvature_eq h (M13.scaleSmoothMetric h Q hQ)
    (Diffeomorph.refl (𝓡 n) N ∞) Q hQ (M13.identity_metricHomothety h Q hQ)
    D' (M13.scaleLeviCivitaData D' Q hQ) (f x))

theorem laplacian_comp_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    {x : M} (hx : x ∈ U) {u : N → ℝ}
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (f x)) :
    D.laplacian (u ∘ f) x = D'.laplacian u (f x) / Q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hb := g.mfderiv_bijective_of_pullback_eq (M13.scaleSmoothMetric h Q hQ) y
      (fun a b => (hmetric y hy a b).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) y
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f y)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : N → Type _) (f y)
    exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f y).toLinearMap
      hb).toContinuousLinearEquiv, rfl⟩
  have hm : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = (M13.scaleSmoothMetric h Q hQ).inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hmetric y hy
  have hlocal := D.laplacian_comp_of_metric_pullback (M13.scaleLeviCivitaData D' Q hQ)
    ((hf x hx).contMDiffAt (hU.mem_nhds hx)) hinv hm hu
  exact hlocal.trans (scaledLeviCivita_laplacian D' hQ hu)

theorem scalarLaplacian_eq_of_local_homothety [T2Space N]
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    {x : M} (hx : x ∈ U) :
    D.laplacian D.scalarCurvature x =
      D'.laplacian D'.scalarCurvature (f x) / Q ^ 2 := by
  have heq : D.scalarCurvature =ᶠ[𝓝 x]
      (fun y => Q⁻¹ * D'.scalarCurvature (f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [div_eq_mul_inv, mul_comm] using
      scalarCurvature_eq_of_local_homothety D D' hQ hU hf hmetric hy
  rw [D.laplacian_eq_of_eventuallyEq heq, D.laplacian_const_mul]
  have hlocal := laplacian_comp_of_local_homothety D D' hQ hU hf hmetric hx
    (D'.contMDiff_scalarCurvature (f x))
  change Q⁻¹ * D.laplacian (D'.scalarCurvature ∘ f) x = _
  rw [hlocal]
  field_simp [hQ.ne']

end LocalHomothety

end PoincareConjecture.M32
