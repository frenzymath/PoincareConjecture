import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped Manifold ContDiff
namespace PoincareConjecture.RiemannianMetric
variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]

theorem inner_symm_of_diffeomorph_metric_pullback
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 m⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 m) e x v) (mfderiv (𝓡 n) (𝓡 m) e x w))
    (y : N) (v w : TangentSpace (𝓡 m) y) :
    gN.inner y v w = gM.inner (e.symm y)
      (mfderiv (𝓡 m) (𝓡 n) e.symm y v) (mfderiv (𝓡 m) (𝓡 n) e.symm y w) := by
  have hcomp := mfderiv_comp y
    (e.contMDiff.mdifferentiable (by simp) (e.symm y))
    (e.symm.contMDiff.mdifferentiable (by simp) y)
  have heq : (e : M → N) ∘ (e.symm : N → M) = id := funext e.apply_symm_apply
  rw [heq, mfderiv_id] at hcomp
  have hv := congrArg (fun A => A v) hcomp
  have hw := congrArg (fun A => A w) hcomp
  have hh := hinner (e.symm y)
    (mfderiv (𝓡 m) (𝓡 n) e.symm y v) (mfderiv (𝓡 m) (𝓡 n) e.symm y w)
  change v = mfderiv (𝓡 n) (𝓡 m) e (e.symm y)
    (mfderiv (𝓡 m) (𝓡 n) e.symm y v) at hv
  change w = mfderiv (𝓡 n) (𝓡 m) e (e.symm y)
    (mfderiv (𝓡 m) (𝓡 n) e.symm y w) at hw
  rw [← hv, ← hw, e.apply_symm_apply] at hh
  exact hh.symm

theorem edist_eq_of_diffeomorph_metric_pullback
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 m⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 m) e x v) (mfderiv (𝓡 n) (𝓡 m) e x w))
    (x y : M) : gN.edist (e x) (e y) = gM.edist x y := by
  apply le_antisymm (edist_map_le_of_metric_pullback gM gN e.contMDiff hinner x y)
  simpa only [e.symm_apply_apply] using
    edist_map_le_of_metric_pullback gN gM e.symm.contMDiff
      (inner_symm_of_diffeomorph_metric_pullback gM gN e hinner) (e x) (e y)
end PoincareConjecture.RiemannianMetric
