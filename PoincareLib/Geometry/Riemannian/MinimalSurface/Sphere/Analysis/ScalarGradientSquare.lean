import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Fields.ScalarChainRule
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.Curvature
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Regularity

/-!
# Intrinsic regularity of the scalar gradient square

Morgan-Tian Claim 18.12, printed pp. 426-427, omitted-pole derivation.
The frozen basis sum is the squared norm of the actual metric gradient,
so smoothness does not depend on a smooth choice of orthonormal basis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The frozen scalar gradient square is the actual metric gradient
norm squared. Source: MT Claim 18.12, pp. 426-427, omitted-pole derivation. -/
theorem scalarGradientSq_eq_inner_gradient (D : LeviCivitaData g) (q : M → ℝ) (p : M) :
    M04.scalarGradientSq g q p = g.inner p (D.gradient q p) (D.gradient q p) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold M04.scalarGradientSq
  simp_rw [← D.inner_gradient]
  change (∑ i, (inner ℝ (D.gradient q p) (g.orthonormalBasis p i)) ^ 2) =
    inner ℝ (D.gradient q p) (D.gradient q p)
  rw [real_inner_self_eq_norm_sq]
  simpa only [real_inner_comm] using (g.orthonormalBasis p).sum_sq_inner_right (D.gradient q p)

/-- The actual gradient square of a smooth scalar is smooth.
Source: MT Claim 18.12, pp. 426-427, omitted-pole derivation. -/
theorem contMDiff_scalarGradientSq (D : LeviCivitaData g) {q : M → ℝ}
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (M04.scalarGradientSq g q) := by
  have heq : M04.scalarGradientSq g q = fun p => g.inner p (D.gradient q p) (D.gradient q p) :=
    funext (scalarGradientSq_eq_inner_gradient D q)
  rw [heq]
  exact D.contMDiff_inner_gradient hq hq

end PoincareMT.M60
