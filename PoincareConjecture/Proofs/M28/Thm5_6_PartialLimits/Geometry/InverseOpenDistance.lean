import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M28

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

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

end PoincareConjecture.M28
