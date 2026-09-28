import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}


theorem scalar_add_laplacian_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ}
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) : D.scalarCurvature x + D.laplacian f x = 2 * lambda := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  unfold scalarCurvature laplacian
  rw [← Finset.sum_add_distrib]
  simp_rw [hsol]
  have hnorm (i) : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 :=
    (g.orthonormalBasis x).inner_eq_ite i i |>.trans (if_pos rfl)
  simp only [hnorm, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    hd, nsmul_eq_mul, Nat.cast_ofNat]

theorem scalar_le_twice_scale_of_potential_min (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hp : IsLocalMin f p) : D.scalarCurvature p ≤ 2 * lambda := by
  have htrace := D.scalar_add_laplacian_of_surface_soliton hsol p
  have hsign := D.horizon_laplacian_nonneg_of_isLocalMin hf hp
  linarith

theorem twice_scale_le_scalar_of_potential_max (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {p : M} (hp : IsLocalMax f p) : 2 * lambda ≤ D.scalarCurvature p := by
  have htrace := D.scalar_add_laplacian_of_surface_soliton hsol p
  have hsign := D.laplacian_nonpos_of_isLocalMax hf hp
  linarith

theorem gradient_eq_zero_of_potential_max (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {p : M} (hp : IsLocalMax f p) : D.gradient f p = 0 := by
  apply (g.inner_isInvertible p).injective
  apply ContinuousLinearMap.ext
  intro v
  rw [D.inner_gradient, mvfderiv_eq_zero_of_isLocalMax hf hp]
  simp

theorem gradient_eq_zero_of_potential_min (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {p : M} (hp : IsLocalMin f p) : D.gradient f p = 0 := by
  have hz := mvfderiv_eq_zero_of_isLocalMax hf.neg hp.neg
  have hd : mvfderiv (𝓡 2) f p = 0 := by
    have heq : (fun x => -f x) = -f := rfl
    rw [heq, mvfderiv_neg] at hz
    exact neg_eq_zero.mp hz
  apply (g.inner_isInvertible p).injective
  apply ContinuousLinearMap.ext
  intro v
  rw [D.inner_gradient, hd]
  simp

end PoincareConjecture.LeviCivitaData
