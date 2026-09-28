import PoincareConjecture.Proofs.M10.PullbackMetric
import Mathlib.Geometry.Manifold.Diffeomorph








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem metric_eq_of_diffeomorph_pullback (g : RiemannianMetric n M)
    (f : Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hmetric : ∀ x v w : EuclideanSpace ℝ (Fin n),
      pullbackMetricForm g f x v w = inner ℝ v w)
    (q : M) (v w : TangentSpace (𝓡 n) q) :
    g.inner q v w = inner ℝ (mfderiv (𝓡 n) (𝓡 n) f.symm q v)
      (mfderiv (𝓡 n) (𝓡 n) f.symm q w) := by
  have hid : (f : EuclideanSpace ℝ (Fin n) → M) ∘ f.symm = id :=
    funext f.apply_symm_apply
  have hcomp (a : TangentSpace (𝓡 n) q) :
      mfderiv (𝓡 n) (𝓡 n) f (f.symm q) (mfderiv (𝓡 n) (𝓡 n) f.symm q a) = a := by
    have h := mfderiv_comp_apply q
      ((f.contMDiffAt (x := f.symm q)).mdifferentiableAt (by simp))
      ((f.symm.contMDiffAt (x := q)).mdifferentiableAt (by simp)) a
    rw [hid, mfderiv_id] at h
    exact h.symm
  have h := hmetric (f.symm q) (mfderiv (𝓡 n) (𝓡 n) f.symm q v)
    (mfderiv (𝓡 n) (𝓡 n) f.symm q w)
  change g.inner (f (f.symm q))
    (mfderiv (𝓡 n) (𝓡 n) f (f.symm q) (mfderiv (𝓡 n) (𝓡 n) f.symm q v))
    (mfderiv (𝓡 n) (𝓡 n) f (f.symm q) (mfderiv (𝓡 n) (𝓡 n) f.symm q w)) = _ at h
  have h' : g.inner (f (f.symm q)) v w =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) f.symm q v)
        (mfderiv (𝓡 n) (𝓡 n) f.symm q w) := by
    simpa only [hcomp] using h
  exact (congrArg (fun y : M ↦ g.inner y v w) (f.apply_symm_apply q)).symm.trans h'

end PoincareConjecture.M10
