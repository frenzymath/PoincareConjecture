import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.TimeDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open scoped Manifold ContDiff Bundle Topology
open Set

namespace PoincareConjecture

theorem movingMetric_hasDerivWithinAt_pair
    {n : ℕ} {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    {g : ℝ → RiemannianMetric n C} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) {t : ℝ} (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t)
    (x : C) {a b : ℝ → EuclideanSpace ℝ (Fin n)} {a' b' : EuclideanSpace ℝ (Fin n)}
    (ha : HasDerivWithinAt a a' J t) (hb : HasDerivWithinAt b b' J t) :
    HasDerivWithinAt (fun s => (g s).inner x (a s) (b s))
      (derivWithin (fun s => (g s).inner x (a t) (b t)) J t +
        (g t).inner x a' (b t) + (g t).inner x (a t) b') J t := by
  let B : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun s => (g s).inner x
  have hB : ContDiffOn ℝ ∞ B J := by
    rw [contDiffOn_clm_apply]
    intro u
    rw [contDiffOn_clm_apply]
    intro v s hs
    exact hg.contDiffWithinAt_inner_time hs x u v
  have hd := ((hB t ht).differentiableWithinAt (by simp)).hasDerivWithinAt
  have hv := (hd.clm_apply (hasDerivWithinAt_const t J (a t))).clm_apply
    (hasDerivWithinAt_const t J (b t))
  have heq : derivWithin (fun s => (g s).inner x (a t) (b t)) J t =
      derivWithin B J t (a t) (b t) := by
    simpa only [map_zero, add_zero, add_apply, B] using! hv.derivWithin hJ
  simpa only [add_apply, ← heq, B] using! (hd.clm_apply ha).clm_apply hb

end PoincareConjecture
