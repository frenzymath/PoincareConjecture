import PoincareLib.Geometry.Riemannian.SpaceForm.LocalIsometry.Comparison
import PoincareLib.Geometry.Riemannian.SpaceForm.SphereCurvature

/-! # Local round isometries from unit sectional curvature -/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Bundle

namespace Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT

/-- Every point of a compact unit-curvature manifold has a smooth round
isometry on an open neighborhood, with any prescribed image on the sphere. -/
theorem exists_local_isometry_unitSphere
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1)
    (p : M) (q : UnitSphere n) :
    ∃ F : OpenPartialHomeomorph M (UnitSphere n),
      p ∈ F.source ∧ F p = q ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target ∧
      ∀ x ∈ F.source, ∀ v w : TangentSpace (𝓡 n) x,
        g.inner x v w = (roundSphereMetric n).inner (F x)
          (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) :=
  PoincareMT.SpaceForm.exists_local_isometry_of_unit_curvature g (roundSphereMetric n)
    g.leviCivitaData (roundSphereMetric n).leviCivitaData hsec
    roundSphereMetric_unit_sectionalCurvature p q

end Poincare.Geometry.Riemannian.SpaceForm
