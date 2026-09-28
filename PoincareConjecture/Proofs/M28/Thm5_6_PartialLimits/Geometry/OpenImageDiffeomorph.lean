import PoincareConjecture.Proofs.M28.Mathlib.PartialDiffeomorphOnOpens
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M28

variable {X : Type u} {N : Type v}
  [TopologicalSpace X] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ N]



theorem edist_eq_intrinsicOpenMetric_of_diffeomorph_pullback
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 N)
    (W : TopologicalSpace.Opens N) (D : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ W)
    (hinner : ∀ (x : X) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (D x : N)
        (mfderiv (𝓡 3) (𝓡 3) ((Subtype.val : W → N) ∘ D) x v)
        (mfderiv (𝓡 3) (𝓡 3) ((Subtype.val : W → N) ∘ D) x w))
    (x y : X) :
    g.edist x y = (intrinsicOpenMetric h W).edist (D x) (D y) := by
  apply RiemannianMetric.edist_diffeomorph g (intrinsicOpenMetric h W) D
  intro z v w
  rw [hinner z v w, intrinsicOpenMetric_inner]
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : W → N) (D z) :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := W) (n := 1)).mdifferentiable
      one_ne_zero (D z)
  rw [mfderiv_comp z hi (D.mdifferentiable (by simp) z)]
  rfl

omit [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ N] in


theorem diffeomorph_openImageMap_isLocalDiffeomorph
    (W : TopologicalSpace.Opens N) (D : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ W) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((Subtype.val : W → N) ∘ D) := by
  intro x
  exact (D.isLocalDiffeomorph x).comp (𝓡 3) N
    (openSubtype_isLocalDiffeomorph W (D x))



theorem pullbackOfLocalDiffeomorph_edist_openImage
    (h : RiemannianMetric 3 N) (W : TopologicalSpace.Opens N)
    (D : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ W) (x y : X) :
    (h.pullbackOfLocalDiffeomorph ((Subtype.val : W → N) ∘ D)
      (diffeomorph_openImageMap_isLocalDiffeomorph W D)).edist x y =
      (intrinsicOpenMetric h W).edist (D x) (D y) := by
  apply edist_eq_intrinsicOpenMetric_of_diffeomorph_pullback
  intro z v w
  rfl

end PoincareConjecture.M28
