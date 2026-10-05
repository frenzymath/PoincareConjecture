import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.MetricNondegeneration
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.MetricContraction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.ScalarNeighborhood
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.MetricSpace
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.HessianTrace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Propagating terminal scalar blowup to the tip

Morgan-Tian Proposition 12.31, pp. 325-326. The direct rotational route
first treats points away from the tip. A bounded terminal scalar at the
tip would give a scalar-radius lower bound on one fixed neighborhood by
the guarded gradient estimate and metric contraction. That neighborhood
contains a nonzero point, contradicting its terminal scalar blowup.
No uniform scalar lower rate is used in this implication.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31, pp. 325-326: actual guarded gradient control
propagates terminal blowup from every nonzero point to the origin. -/
theorem scalar_tendsto_at_origin_of_tendsto_off_origin
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    {A H : ℝ} (hA : 0 < A)
    (hgrad : ∀ t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      H ≤ (E.flow.connection t).scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, (E.flow.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (E.flow.connection t).scalarCurvature x v| ≤
          A * (E.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ))
    (hoff : ∀ x : StandardCapSpace, x ≠ 0 →
      Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop) :
    Tendsto (fun t => (E.flow.connection t).scalarCurvature 0) (𝓝[<] 1) atTop := by
  by_contra hnot
  obtain ⟨B, hB, hbound⟩ := E.exists_final_scalar_bound_of_not_tendsto P 0 hnot
  let K := max B H
  have hK : 0 < K := hB.trans_le (le_max_left _ _)
  let r := K ^ (-1 / 2 : ℝ) / A
  have hr : 0 < r := div_pos (Real.rpow_pos_of_pos hK _) hA
  let g := E.flow.metric (1 / 2)
  have hball : g.ball 0 r ∈ 𝓝 (0 : StandardCapSpace) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    exact eventually_riemannianEDist_lt (𝓡 3) 0 (ENNReal.ofReal_pos.mpr hr)
  obtain ⟨y, hyne, hyball⟩ := (dense_compl_singleton (0 : StandardCapSpace)).exists_mem_open
    isOpen_interior ⟨0, mem_interior_iff_mem_nhds.mpr hball⟩
  have hyne' : y ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hyne
  have hy : y ∈ g.ball 0 r := interior_subset hyball
  have hhalf : (1 / 2 : ℝ) ∈ Ico 0 E.flow.base.lifetime := by
    rw [E.lifetime_one]
    norm_num
  have hpositive : 0 < K ^ (-1 / 2 : ℝ) / 2 := half_pos (Real.rpow_pos_of_pos hK _)
  have hzero : Tendsto
      (fun t => (E.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ))
      (𝓝[<] 1) (𝓝 0) := by
    have hcomp :=
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp (hoff y hyne')
    convert hcomp using 1
    ext t
    simp only [Function.comp_apply, neg_div]
  have hle : K ^ (-1 / 2 : ℝ) / 2 ≤ 0 := by
    apply ge_of_tendsto hzero
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with t ht hhalfT
    have htmem : t ∈ Ico 0 E.flow.base.lifetime :=
      ⟨by linarith, E.lifetime_one.symm ▸ ht⟩
    have hytime : y ∈ (E.flow.metric t).ball 0 r :=
      E.ball_subset_of_time_le hhalf htmem hhalfT.le 0 r hy
    exact M35.scalar_radius_lower_on_ball (E.flow.metric t) (E.flow.connection t)
      (E.scalar_pos htmem) (Proofs.M09.scalarCurvature_contMDiff P (E.flow.connection t))
      hA hK (le_max_right _ _) (hgrad t htmem)
      ((hbound t ⟨hhalfT.le, ht⟩).trans (le_max_left _ _)) hytime
  exact not_lt_of_ge hle hpositive

end PoincareMT.RepairedStandardCapExistenceData
