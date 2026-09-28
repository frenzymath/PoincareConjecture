import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.PastControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u
namespace PoincareConjecture.M22UniversalNoncollapsingPredecessors

variable {d n : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] (K : AncientKappaSolution n M)

include H

theorem scalar_monotone {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0) (x : M) :
    (K.flow.connection s).scalarCurvature x ≤ (K.flow.connection t).scalarCurvature x := by
  apply K.scalar_monotone_of_differential
    (H.ancient_differential n M K.flow K.complete K.nonnegative_curvature_operator
      (fun t ht ↦ K.operator_bound_of_tensor_calculus t ht
        (H.tensor_calculus n M _ _)) K.nonflat) s t hst ht x

theorem complete_bounded_on {J : Set ℝ} (hJ : J ⊆ Iic (0 : ℝ)) :
    CompleteBoundedCurvatureOn K.flow J := by
  obtain ⟨C, hC, hbound⟩ := K.whole_past_bound_of_scalar_monotone
    (fun t _ ↦ H.tensor_calculus n M _ _)
    (fun _ _ hst ht x ↦ H.scalar_monotone K hst ht x)
  refine ⟨fun t ht ↦ K.complete t (hJ ht), C, hC, fun t ht x ↦ ?_⟩
  rw [abs_of_nonneg (by unfold LeviCivitaData.curvatureTensorNorm; positivity)]
  exact hbound t (hJ ht) x

theorem metric_inner_le_exp_four {s : ℝ} (hs : s ∈ Icc (-2 : ℝ) (-1))
    (x : M) (hx : (K.flow.connection (-1)).scalarCurvature x ≤ 2)
    (v : TangentSpace (𝓡 n) x) :
    (K.flow.metric s).inner x v v ≤ Real.exp 4 * (K.flow.metric (-1)).inner x v v := by
  have hnonneg (t : ℝ) : 0 ≤ (K.flow.metric t).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((K.flow.metric t).pos x v hv).le
  have hRic (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) (-1)) :
      |(K.flow.connection t).ricci x v v| ≤ 2 * (K.flow.metric t).inner x v v := by
    have ht0 : t ≤ 0 := ht.2.trans (by norm_num)
    have hbound := (K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (H.tensor_calculus n M _ _) x (K.nonnegative_curvature_operator t ht0 x) v
    rw [abs_of_nonneg hbound.1]
    exact hbound.2.trans (mul_le_mul_of_nonneg_right
      ((H.scalar_monotone K ht.2 (by norm_num) x).trans hx) (hnonneg t))
  have hcomp := (K.flow.metric_inner_self_exp_bounds (convex_Icc (-2) (-1))
    (fun t ht ↦ ht.2.trans (by norm_num)) x v 2 hRic
    (a := -1) (by norm_num) hs).2
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_right _ (hnonneg (-1))
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonpos (by linarith [hs.2] : s - -1 ≤ 0)]
  linarith [hs.1]

end PoincareConjecture.M22UniversalNoncollapsingPredecessors
