import PoincareLib.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareLib.Geometry.Riemannian.Curvature.LocalSecondBianchi
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Radial curvature and its Ricci trace

The radial Jacobi operator uses `R(u,v)v`. The retained four-covariant
convention is `g(R(u,v)z,w)`, so both skew symmetries identify its trace
with the retained Ricci contraction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Bundle VectorField

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Curvature in the radial direction as a linear operator. -/
noncomputable def radialCurvature (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine { toFun := fun u => D.curvature x u v v, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply ext_inner_right ℝ
    intro w
    rw [inner_add_left]
    exact D.curvatureTensor_add_first x a b v w v
  · intro c a
    apply ext_inner_right ℝ
    intro w
    rw [real_inner_smul_left]
    exact D.curvatureTensor_smul_first x c a v w v

@[simp] theorem radialCurvature_apply (D : LeviCivitaData g) (x : M)
    (v u : TangentSpace (𝓡 n) x) :
    D.radialCurvature x v u = D.curvature x u v v := rfl

/-- The radial vector lies in the kernel of radial curvature. -/
@[simp] theorem radialCurvature_self (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) : D.radialCurvature x v v = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  rw [inner_zero_left]
  exact D.curvatureTensor_zero_first x v w v

/-- The full radial-curvature trace equals the retained Ricci quadratic form. -/
theorem trace_radialCurvature (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    LinearMap.trace ℝ (TangentSpace (𝓡 n) x) (D.radialCurvature x v) =
      D.ricci x v v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
  unfold ricci
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  change D.curvatureTensor x (g.orthonormalBasis x i) v
      (g.orthonormalBasis x i) v = _
  rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]

end PoincareMT.LeviCivitaData
