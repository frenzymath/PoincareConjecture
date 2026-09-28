import PoincareConjecture.Proofs.M47.GeneralizedBridgeGeometry
import PoincareConjecture.Proofs.M35.Mathlib.DiffeomorphDerivative
import PoincareConjecture.Definitions.M13MetricHomothety










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47


theorem metricHomothety_one_symm
    {n : ℕ} {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X]
    {g : RiemannianMetric n M} {h : RiemannianMetric n X}
    (f : Diffeomorph (𝓡 n) (𝓡 n) M X ∞) (hf : MetricHomothety g h f 1) :
    MetricHomothety h g f.symm 1 := by
  intro y v w
  have hd := f.mfderiv_cancel_left (I₁ := 𝓡 n) (by simp) (id : X → X) y
  simp only [Function.comp_id, id_eq, mfderiv_id] at hd
  have hmetric := hf (f.symm y) (mfderiv (𝓡 n) (𝓡 n) f.symm y v)
    (mfderiv (𝓡 n) (𝓡 n) f.symm y w)
  change h.inner (f (f.symm y))
    (((mfderiv (𝓡 n) (𝓡 n) f (f.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) f.symm y)) v)
    (((mfderiv (𝓡 n) (𝓡 n) f (f.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) f.symm y)) w) = _ at hmetric
  rw [hd] at hmetric
  change h.inner (f (f.symm y)) v w = 1 * g.inner (f.symm y)
    (mfderiv (𝓡 n) (𝓡 n) f.symm y v) (mfderiv (𝓡 n) (𝓡 n) f.symm y w) at hmetric
  rw [f.apply_symm_apply, one_mul] at hmetric
  simpa only [one_mul] using hmetric.symm

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
  (hregular : t ∉ F.surgery_times)



theorem regular_history_inverse_homothety :
    MetricHomothety (F.metric t) (H.generalized.metric t)
      (regular_history_slice_diffeomorph H t ht hregular).symm 1 := by
  apply metricHomothety_one_symm
  intro x v w
  change (F.metric t).inner (H.history.forward t ht x)
    (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) x v)
    (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) x w) =
      1 * (H.generalized.metric t).inner x v w
  rw [one_mul]
  exact H.history.metric_pullback t ht x v w

end PoincareConjecture.M47
