import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenNeckRestriction
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareLib.Geometry.Manifold.RegularLevel.OpenInclusion

/-!
# Curvature-derivative naturality for open metric restrictions

The intrinsic metric on an open subtype is the literal pullback of the
ambient metric.  This file records the all-order curvature-norm identity
needed when a source strong-neck connection is compared with the retained
tube connection.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- Every Levi-Civita connection on an intrinsic open restriction has the
same curvature-derivative norms as the ambient connection at the lifted
point.  The proof uses only the open-subtype differential and the literal
pullback metric identity. -/
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
    (PoincareMT.LeviCivitaData.curvatureDerivativeNorm_eq_pullback DU D
      isOpen_univ hf hinv hmetric m (x := x) (mem_univ x))

end PoincareMT.M28
