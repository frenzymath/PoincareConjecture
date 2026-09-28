import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter Function

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem ricciReaction_symm (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.ricciReaction x u v = D.ricciReaction x v u := by
  let b := g.orthonormalBasis x
  have hDouble :
      (∑ i, ∑ j, D.curvatureTensor x v (b i) u (b j) *
        D.ricci x (b i) (b j)) =
      ∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) *
        D.ricci x (b i) (b j) := by
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [curvatureTensor_pair_exchange D x v (b j) u (b i)]
    rw [ricci_symm D x (b j) (b i)]
  have hSquare :
      (∑ i, D.ricci x v (b i) * D.ricci x (b i) u) =
      ∑ i, D.ricci x u (b i) * D.ricci x (b i) v := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ricci_symm D x v (b i), ricci_symm D x (b i) u]
    ring
  unfold LeviCivitaData.ricciReaction
  simpa only [b] using congrArg₂ (fun a c : ℝ ↦ 2 * a - 2 * c) hDouble.symm hSquare.symm

end PoincareConjecture.RicciFlowAnalysis
