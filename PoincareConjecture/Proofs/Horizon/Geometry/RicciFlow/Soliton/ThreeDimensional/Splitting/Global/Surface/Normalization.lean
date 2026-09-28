import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Normalization










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [CompactSpace M] {g : RiemannianMetric 2 M}



theorem compactRoundSurface_sectionalCurvature_of_soliton
    (D : LeviCivitaData g) {φ : M → ℝ} {lambda : ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = lambda * g.inner x u v)
    (hround : ConstantPositiveSectionalCurvature g D)
    (x : M) (u v : TangentSpace (𝓡 2) x)
    (hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0) :
    D.sectionalCurvature x u v = lambda := by
  rw [D.sectionalCurvature_eq_half_scalarCurvature x u v hgram,
    D.scalar_eq_twice_scale_of_compact_round_soliton hφ hsol hround]
  ring


theorem compactRoundSurface_ricci_of_soliton
    (D : LeviCivitaData g) {φ : M → ℝ} {lambda : ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = lambda * g.inner x u v)
    (hround : ConstantPositiveSectionalCurvature g D)
    (x : M) (u v : TangentSpace (𝓡 2) x) :
    D.ricci x u v = lambda * g.inner x u v := by
  rw [D.ricci_eq_half_scalarCurvature_mul_inner,
    D.scalar_eq_twice_scale_of_compact_round_soliton hφ hsol hround]
  ring


theorem compactRoundSurface_hessian_eq_zero_of_soliton
    (D : LeviCivitaData g) {φ : M → ℝ} {lambda : ℝ}
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 2) x,
      D.ricci x u v + D.hessian φ x u v = lambda * g.inner x u v)
    (hround : ConstantPositiveSectionalCurvature g D)
    (x : M) (u v : TangentSpace (𝓡 2) x) :
    D.hessian φ x u v = 0 := by
  have heq := hsol x u v
  rw [compactRoundSurface_ricci_of_soliton D hφ hsol hround] at heq
  linarith

end PoincareConjecture.RicciFlow.Splitting
