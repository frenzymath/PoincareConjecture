import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction.Symmetry


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma tensorHeatOperator_riemann
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    F.tensorHeatOperator (fun s => (F.connection s).riemannEvaluation)
        t x ![a, b, c, d] =
      2 * (D.curvatureB x a b c d - D.curvatureB x a b d c -
        D.curvatureB x a d b c + D.curvatureB x a c b d) := by
  classical
  let D := F.connection t
  let e := (F.metric t).orthonormalBasis x
  have hd := (hC.curvature_evolution n M J F t (interior_subset ht) x a b c d).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have ha : D.ricciTensorAction D.riemannEvaluation x ![a, b, c, d] =
      (∑ i, D.ricci x a (e i) * D.curvatureTensor x (e i) b c d) +
      (∑ i, D.ricci x b (e i) * D.curvatureTensor x a (e i) c d) +
      (∑ i, D.ricci x c (e i) * D.curvatureTensor x a b (e i) d) +
      (∑ i, D.ricci x d (e i) * D.curvatureTensor x a b c (e i)) := by
    unfold LeviCivitaData.ricciTensorAction
    rw [Fin.sum_univ_four]
    simp [LeviCivitaData.riemannEvaluation, Function.update, e]
  dsimp only
  unfold tensorHeatOperator
  change deriv (fun s => (F.connection s).curvatureTensor x a b c d) t +
    D.ricciTensorAction D.riemannEvaluation x ![a, b, c, d] -
    D.tensorLaplacian D.riemannEvaluation x ![a, b, c, d] = _
  rw [hd.deriv, ha]
  dsimp only [LeviCivitaData.curvatureReaction, D, e]
  simp only [Finset.sum_add_distrib]
  ring

end PoincareConjecture.RicciFlow
