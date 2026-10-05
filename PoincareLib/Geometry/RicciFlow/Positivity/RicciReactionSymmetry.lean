import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareLib.Geometry.RicciFlow.Curvature.Reaction

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04/RicciReactionSymmetry.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Symmetry of the corrected Ricci reaction

The frozen quadratic Ricci reaction is symmetric in its two tangent inputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter Function

universe u

namespace PoincareMT.RicciFlowAnalysis

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

end PoincareMT.RicciFlowAnalysis
