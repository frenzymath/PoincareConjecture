import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Control







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RicciFlow

private theorem metric_eq_of_inner_eq
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g h : RiemannianMetric n M)
    (heq : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w = h.inner x v w) :
    g = h := by
  have hi : g.inner = h.inner := by
    funext x
    exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => heq x v w
  cases g
  cases h
  cases hi
  rfl



theorem ancientRescaleAt_backward_metric_zero
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (F : RicciFlow n M (Iic 0)) (c : ℝ) (hc : 0 < c) (Q : ℝ) (hQ : 0 < Q)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (htback : t₀ - 1 / Q ≤ 0) :
    (F.ancientRescaleAt (c * Q) (mul_pos hc hQ) (t₀ - 1 / Q) htback).metric 0 =
      rescaledMetric ((F.ancientRescaleAt Q hQ t₀ ht₀).metric (-1)) c hc := by
  apply metric_eq_of_inner_eq
  intro x v w
  simp only [ancientRescaleAt_metric, zero_div, add_zero, rescaledMetric_inner]
  have ht : t₀ - 1 / Q = t₀ + (-1) / Q := by ring
  rw [ht]
  ring

end PoincareConjecture.RicciFlow
