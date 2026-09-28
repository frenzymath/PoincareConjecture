import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenNeckRestriction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]





theorem intrinsicOpenMetric_curvatureDerivativeNorm
    (g : RiemannianMetric 3 M) (V : TopologicalSpace.Opens M)
    (DU : LeviCivitaData (intrinsicOpenMetric g V))
    (D : LeviCivitaData g) (m : ℕ) (x : V) :
    DU.curvatureDerivativeNorm m x = D.curvatureDerivativeNorm m (x : M) := by
  let f : V → M := (Subtype.val : V → M)
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Set.univ : Set V) :=
    contMDiff_subtype_val.contMDiffOn
  have hinv : ∀ y : V, y ∈ (Set.univ : Set V) →
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    intro y hy
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal V y]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hmetric : ∀ y : V, y ∈ (Set.univ : Set V) →
      ∀ u v : TangentSpace (𝓡 3) y,
        (intrinsicOpenMetric g V).inner y u v =
          g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
            (mfderiv (𝓡 3) (𝓡 3) f y v) := by
    intro y hy u v
    exact intrinsicOpenMetric_inner g V y u v
  simpa only [f] using
    (PoincareConjecture.LeviCivitaData.curvatureDerivativeNorm_eq_pullback DU D
      isOpen_univ hf hinv hmetric m (x := x) (mem_univ x))

end PoincareConjecture.M28
