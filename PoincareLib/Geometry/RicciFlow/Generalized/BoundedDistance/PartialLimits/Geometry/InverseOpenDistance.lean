import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicOpenMetric
import PoincareLib.Geometry.Riemannian.Distance.TangentBound

/-!
# Distance control for the actual inverse on an open source image

A lower quadratic bound on a partial diffeomorphism bounds its inverse
on any open subset of the true target. The metric on that subset is the
literal open pullback metric. Source: Morgan--Tian Theorem 5.6, pp. 85-87;
M28 derivation 122. The integration step reuses the published differential
distance theorem also used by M25's round-sphere distortion proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareMT.M28

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

/-- A quadratic forward lower bound controls the actual smooth inverse
in intrinsic open distance. No inverse is tested outside its target.
Source: Theorem 5.6, pp. 85-87; M28 derivation 122. -/
theorem inverse_edist_le_intrinsicOpenMetric
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ e.target)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ y ∈ (U : Set N), ∀ v : TangentSpace (𝓡 3) (e.symm y),
      g.inner (e.symm y) v v ≤ C ^ 2 * h.inner (e (e.symm y))
        (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) v)
        (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) v)) (p q : U) :
    g.edist (e.symm (p : N)) (e.symm (q : N)) ≤
      ENNReal.ofReal C * (intrinsicOpenMetric h U).edist p q := by
  let F : U → M := e.symm ∘ Subtype.val
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := by
    intro z
    exact ((e.symm.contMDiffOn z (hU z.property)).contMDiffAt
      (e.open_target.mem_nhds (hU z.property))).comp z
        (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffAt
  have hright : (e ∘ F) = (Subtype.val : U → N) := by
    funext z
    exact e.toPartialEquiv.right_inv (hU z.property)
  apply (intrinsicOpenMetric h U).edist_le_mul_of_inner_mfderiv_le g
    (hF.of_le (by simp)) hC _ p q
  intro z v
  have hcomp := mfderiv_comp z
    (e.mdifferentiableAt (by simp) (e.toPartialEquiv.map_target (hU z.property)))
    (hF.mdifferentiable (by simp) z)
  rw [hright] at hcomp
  have hv : mfderiv (𝓡 3) (𝓡 3) e (F z)
      (mfderiv (𝓡 3) (𝓡 3) F z v) =
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → N) z v :=
    (congrArg (fun A => A v) hcomp).symm
  have hb := hbound z z.property (mfderiv (𝓡 3) (𝓡 3) F z v)
  change g.inner (F z) _ _ ≤ C ^ 2 * h.inner (e (F z))
    (mfderiv (𝓡 3) (𝓡 3) e (F z) (mfderiv (𝓡 3) (𝓡 3) F z v))
    (mfderiv (𝓡 3) (𝓡 3) e (F z) (mfderiv (𝓡 3) (𝓡 3) F z v)) at hb
  rw [hv, show e (F z) = (z : N) from congrFun hright z] at hb
  exact hb

end PoincareMT.M28
