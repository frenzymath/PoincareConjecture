import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeScaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Ricci








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma tensorHeatOperator_ricci_timeCorrection
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    F.tensorHeatOperator (fun s y z => (F.connection s).ricciEvaluation y z / (2 * (s - T₀)))
        t x ![u, v] =
      2 * (∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) *
        (D.ricci x (b i) (b j) / (2 * (t - T₀)))) -
      D.ricci x u v / (2 * (t - T₀) ^ 2) := by
  let D := F.connection t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hf := (((hasDerivAt_id t).sub_const T₀).const_mul 2).inv
    (mul_ne_zero (by norm_num) hτ)
  have hd := (hC.ricci_evolution n M J F t (interior_subset ht) x u v).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have heq : (fun s y z => (F.connection s).ricciEvaluation y z / (2 * (s - T₀))) =
      (fun s y z => (2 * (s - T₀))⁻¹ * (F.connection s).ricciEvaluation y z) := by
    funext s y z
    rw [div_eq_mul_inv, mul_comm]
  dsimp only
  rw [heq]
  have h := F.tensorHeatOperator_time_mul (T := fun s => (F.connection s).ricciEvaluation)
    hf hD.2.1 (hD.2.2.1 _ _ hD.2.1)
    x ![u, v] hd.differentiableAt
  simp only [Pi.inv_apply, id_eq, mul_one] at h
  rw [h, F.tensorHeatOperator_ricci hC ht]
  simp only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← mul_div_assoc, ← Finset.sum_div]
  field_simp [hτ]
  ring

end Poincare.RicciFlow.Harnack
