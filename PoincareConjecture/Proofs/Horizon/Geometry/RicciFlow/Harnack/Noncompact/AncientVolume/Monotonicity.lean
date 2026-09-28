import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.Geometry.RicciFlow.Harnack

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem scalarEvolution_nonneg_of_bounded_ancient
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ≤ 0, ∀ x,
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x := by
  intro t ht x
  obtain ⟨dR, hdR, hineq⟩ :=
    F.ancient_differential_of_bounded_ancient hC hcomplete hoperator hK hbound t ht x 0
  have hid : dR = (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x :=
    (hdR.derivWithin (uniqueDiffOn_Iic 0 t ht)).symm.trans
      ((hC.scalar_evolution n M (Iic 0) F t ht x).derivWithin (uniqueDiffOn_Iic 0 t ht))
  rw [← hid]
  have hzero : (F.connection t).ricci x 0 0 = 0 := by
    rw [(F.connection t).ricci_eq_sum_frame x 0 0]
    simp
  simpa only [hzero, map_zero, mul_zero, add_zero] using hineq



theorem scalarCurvature_monotoneOn_of_bounded_ancient
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ x : M, MonotoneOn (fun t => (F.connection t).scalarCurvature x) (Iic 0) := by
  intro x
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic 0)
    (scalarCurvature_continuousOn_time hC (Iic 0) F x)
    (f' := fun t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x)
  · intro t ht
    exact (hC.scalar_evolution n M (Iic 0) F t (interior_subset ht) x).mono interior_subset
  · intro t ht
    exact scalarEvolution_nonneg_of_bounded_ancient hC F hcomplete hoperator hK hbound
      t (show t ∈ Iic (0 : ℝ) from interior_subset ht) x

end PoincareConjecture.RicciFlow
