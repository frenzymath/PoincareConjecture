import PoincareConjecture.Proofs.M03.CurvatureHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff

namespace PoincareConjecture.M34

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def curvatureTrilinearMap (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  Classical.choose (Proofs.M03.exists_curvature_continuousTrilinearMap D x)

theorem curvatureTrilinearMap_apply (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    curvatureTrilinearMap D x u v w = D.curvature x u v w :=
  Classical.choose_spec (Proofs.M03.exists_curvature_continuousTrilinearMap D x) u v w

end PoincareConjecture.M34
