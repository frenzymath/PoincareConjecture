import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option backward.isDefEq.respectTransparency false in

theorem normalized_forward_differential_bound (g : RiemannianMetric n M)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Y)
    {f : EuclideanSpace ℝ (Fin n) → M} {y : Y}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (L.symm y)) {r : ℝ}
    (hbound : ∀ v, g.tangentNorm (f (L.symm y))
      (mfderiv (𝓡 n) (𝓡 n) f (L.symm y) v) ≤ r * ‖L v‖)
    (v : Y) :
    g.tangentNorm ((f ∘ L.symm) y)
      (mfderiv 𝓘(ℝ, Y) (𝓡 n) (f ∘ L.symm) y v) ≤ r * ‖v‖ := by
  rw [mfderiv_comp y hf L.symm.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, L.symm.fderiv]
  change g.tangentNorm (f (L.symm y))
    (mfderiv (𝓡 n) (𝓡 n) f (L.symm y) (L.symm v)) ≤ r * ‖v‖
  simpa only [L.apply_symm_apply] using hbound (L.symm v)

set_option backward.isDefEq.respectTransparency false in

theorem normalized_inverse_differential_bound (g : RiemannianMetric n M)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Y)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : e.MDifferentiable (𝓡 n) (𝓡 n)) {q : M} (hq : q ∈ e.target)
    {r : ℝ} (hr : 0 < r)
    (hbound : ∀ v, ‖L v‖ / r ≤ g.tangentNorm (e (e.symm q))
      (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) v))
    (v : TangentSpace (𝓡 n) q) :
    ‖mvfderiv (𝓡 n) (L ∘ e.symm) q v‖ ≤ r * g.tangentNorm q v := by
  have hcomp := congrArg (fun D ↦ D v) (he.comp_symm_deriv hq)
  change mfderiv (𝓡 n) (𝓡 n) e (e.symm q)
    (mfderiv (𝓡 n) (𝓡 n) e.symm q v) = v at hcomp
  have h := hbound (mfderiv (𝓡 n) (𝓡 n) e.symm q v)
  rw [hcomp, e.right_inv hq] at h
  have hchain : mvfderiv (𝓡 n) (L ∘ e.symm) q v =
      L (mfderiv (𝓡 n) (𝓡 n) e.symm q v) := by
    change mfderiv (𝓡 n) 𝓘(ℝ, Y) (L ∘ e.symm) q v = _
    rw [mfderiv_comp q L.differentiableAt.mdifferentiableAt
      (he.mdifferentiableAt_symm hq), mfderiv_eq_fderiv, L.fderiv]
    rfl
  rw [hchain]
  change ‖L (mfderiv (𝓡 n) (𝓡 n) e.symm q v)‖ ≤ r * g.tangentNorm q v
  exact (div_le_iff₀ hr).mp h |>.trans_eq (mul_comm _ _)

end PoincareConjecture.M10
