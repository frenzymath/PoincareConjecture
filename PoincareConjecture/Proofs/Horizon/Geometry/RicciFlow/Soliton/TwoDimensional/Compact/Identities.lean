import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace LeviCivitaData


theorem ricci_eq_half_scalarCurvature_mul_inner {g : RiemannianMetric 2 M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 2) x) :
    D.ricci x u v = D.scalarCurvature x / 2 * g.inner x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  have hnorm (i) : g.inner x (b i) (b i) = 1 := b.inner_eq_ite i i |>.trans (if_pos rfl)
  have hparseval : (∑ i, g.inner x u (b i) * g.inner x (b i) v) = g.inner x u v :=
    b.sum_inner_mul_inner u v
  dsimp only [b] at hnorm hparseval
  unfold ricci
  simp_rw [D.curvatureTensor_eq_half_scalarCurvature, hnorm, mul_one]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hparseval]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hd, nsmul_eq_mul]
  ring

end LeviCivitaData

namespace GradientShrinkingSolitonData

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem hessian_potential_eq_scalar (S : GradientShrinkingSolitonData 2 M)
    (x : M) (u v : TangentSpace (𝓡 2) x) :
    S.connection.hessian S.potential x u v =
      (1 - S.connection.scalarCurvature x) / 2 * S.metric.inner x u v := by
  have h := S.soliton_equation x u v
  rw [S.connection.ricci_eq_half_scalarCurvature_mul_inner] at h
  linarith


theorem scalarCurvature_add_laplacian_potential (S : GradientShrinkingSolitonData 2 M)
    (x : M) : S.connection.scalarCurvature x + S.connection.laplacian S.potential x = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  let b := S.metric.orthonormalBasis x
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  have hnorm (i) : S.metric.inner x (b i) (b i) = 1 :=
    b.inner_eq_ite i i |>.trans (if_pos rfl)
  dsimp only [b] at hnorm
  unfold LeviCivitaData.laplacian
  simp_rw [S.hessian_potential_eq_scalar, hnorm, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hd, nsmul_eq_mul]
  ring

end GradientShrinkingSolitonData

end PoincareConjecture
