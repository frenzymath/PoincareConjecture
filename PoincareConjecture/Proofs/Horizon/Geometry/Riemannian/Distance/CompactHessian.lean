import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Norm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_metric_hessian_bound_on_compact (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {S : Set M} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ B * g.inner x v v := by
  let H : M → ℝ := fun x => Real.sqrt (∑ i, ∑ j, (D.hessian f x
    (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2)
  have hH : Continuous H := Real.continuous_sqrt.comp (D.contMDiff_hessian_normSq hf).continuous
  obtain ⟨B, hB⟩ := hS.bddAbove_image hH.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro x hx v
  apply (D.abs_hessian_quadratic_le_normSq (hf x) v).trans
  have hHx : H x ≤ max 0 B := (hB ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  apply mul_le_mul_of_nonneg_right hHx
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

theorem exists_metric_hessian_bound_of_hasCompactSupport (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x (v : TangentSpace (𝓡 n) x),
      |D.hessian f x v v| ≤ B * g.inner x v v := by
  obtain ⟨B, hB, hbound⟩ := D.exists_metric_hessian_bound_on_compact hf hc
  refine ⟨B, hB, ?_⟩
  intro x v
  by_cases hx : x ∈ tsupport f
  · exact hbound x hx v
  · have heq := notMem_tsupport_iff_eventuallyEq.mp hx
    rw [D.hessian_eq_of_eventuallyEq heq]
    have hzero : D.hessian (fun _ : M => (0 : ℝ)) x v v = 0 := by
      simp only [hessian, hessianOnFields, mvfderiv_const, zero_apply, sub_self]
    change |D.hessian (fun _ : M => (0 : ℝ)) x v v| ≤ B * g.inner x v v
    rw [hzero, abs_zero]
    apply mul_nonneg hB
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le

end PoincareConjecture.LeviCivitaData
