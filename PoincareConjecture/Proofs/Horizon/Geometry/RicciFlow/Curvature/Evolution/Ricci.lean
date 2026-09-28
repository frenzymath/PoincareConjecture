import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma tensorHeatOperator_ricci
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (u v : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    F.tensorHeatOperator (fun s => (F.connection s).ricciEvaluation) t x ![u, v] =
      2 * ∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) * D.ricci x (b i) (b j) := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hd := (hC.ricci_evolution n M J F t (interior_subset ht) x u v).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have ha := D.ricciTensorAction_two D.ricciEvaluation x u v
  simp only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one] at ha
  have hact : D.ricciTensorAction D.ricciEvaluation x ![u, v] =
      2 * ∑ i, D.ricci x u (b i) * D.ricci x (b i) v := by
    rw [ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hD.2.2.2.1 x v (b i) u v).2.2.2]
    ring
  dsimp only
  unfold tensorHeatOperator
  change deriv (fun s => (F.connection s).ricci x u v) t +
    D.ricciTensorAction D.ricciEvaluation x ![u, v] -
    D.tensorLaplacian D.ricciEvaluation x ![u, v] = _
  rw [hd.deriv, hact]
  dsimp only [LeviCivitaData.ricciReaction, D, b]
  ring

end PoincareConjecture.RicciFlow
