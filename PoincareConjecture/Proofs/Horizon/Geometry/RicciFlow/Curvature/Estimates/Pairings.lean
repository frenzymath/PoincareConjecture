import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Energy.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
theorem abs_tensorPairing_le_tensorNorm_mul {r : ℕ}
    (S T : CovariantTensorEvaluation n M r) (x : M) :
    |tensorPairing g S T x| ≤ g.tensorNorm S x * g.tensorNorm T x := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let f : (Fin r → Fin d) → ℝ := fun a ↦ S x (fun i ↦ b (a i))
  let q : (Fin r → Fin d) → ℝ := fun a ↦ T x (fun i ↦ b (a i))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f q
  have hS : (∑ a : Fin r → Fin d, f a ^ 2) = (g.tensorNorm S x) ^ 2 := by
    change (∑ a : Fin r → Fin d,
      (S x (fun i ↦ b (a i))) ^ 2) = _
    exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).symm
  have hT : (∑ a : Fin r → Fin d, q a ^ 2) = (g.tensorNorm T x) ^ 2 := by
    change (∑ a : Fin r → Fin d,
      (T x (fun i ↦ b (a i))) ^ 2) = _
    exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).symm
  have hsq : |∑ a : Fin r → Fin d, f a * q a| ^ 2 ≤
      (g.tensorNorm S x * g.tensorNorm T x) ^ 2 := by
    rw [sq_abs, mul_pow]
    simpa only [hS, hT] using hcs
  have hnonS : 0 ≤ g.tensorNorm S x := Real.sqrt_nonneg _
  have hnonT : 0 ≤ g.tensorNorm T x := Real.sqrt_nonneg _
  have hprod : 0 ≤ g.tensorNorm S x * g.tensorNorm T x :=
    mul_nonneg hnonS hnonT
  change |∑ a : Fin r → Fin d, f a * q a| ≤ _
  nlinarith [hsq, abs_nonneg (∑ a : Fin r → Fin d, f a * q a)]

end PoincareConjecture.RicciFlowAnalysis
