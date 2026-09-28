import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.LimitNoncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientLimitFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem continuous_scalarCurvature (hC : RicciFlowCurvatureTheory.{u})
    (L : AncientLimitFlow 3) (t : ℝ) :
    Continuous (L.flow.connection t).scalarCurvature := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.carrier.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ L.carrier.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.carrier.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) L.carrier.carrier
  let G : RicciFlow 3 (ULift.{u} L.carrier.carrier) (Iio 0) := L.flow.ulift
  have hc := (hC.tensor_calculus 3 _ (G.metric t) (G.connection t)).contMDiff_scalarCurvature.continuous
  have hup : Continuous (ULift.up : L.carrier.carrier → ULift.{u} L.carrier.carrier) :=
    Homeomorph.ulift.symm.continuous
  simpa only [Function.comp_def, G, L.flow.ulift_scalarCurvature] using hc.comp hup

theorem bddAbove_scalarCurvature_iff_bounded_curvature
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientLimitFlow 3)
    (t : ℝ) (ht : t < 0) :
    BddAbove (range (L.flow.connection t).scalarCurvature) ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.carrier.carrier,
        |(L.flow.connection t).curvatureTensorNorm x| ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨9 * max B 0, by positivity, fun x => ?_⟩
    have hnonneg : 0 ≤ (L.flow.connection t).curvatureTensorNorm x := Real.sqrt_nonneg _
    rw [abs_of_nonneg hnonneg]
    apply (L.curvatureTensorNorm_le_scalarCurvature hC t ht x).trans
    exact mul_le_mul_of_nonneg_left
      ((hB (mem_range_self x)).trans (le_max_left B 0)) (by norm_num)
  · rintro ⟨B, _, hbound⟩
    refine ⟨3 * B, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hs := (L.flow.connection t).scalarCurvature_le_curvatureTensorNorm_sharp x
    norm_num at hs
    have hn := (le_abs_self ((L.flow.connection t).curvatureTensorNorm x)).trans (hbound x)
    linarith

theorem bounded_curvature_of_compact (hC : RicciFlowCurvatureTheory.{u})
    (L : AncientLimitFlow 3) [CompactSpace L.carrier.carrier]
    (t : ℝ) (ht : t < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.carrier.carrier,
      |(L.flow.connection t).curvatureTensorNorm x| ≤ B := by
  apply (L.bddAbove_scalarCurvature_iff_bounded_curvature hC t ht).mp
  simpa only [image_univ] using
    isCompact_univ.bddAbove_image (L.continuous_scalarCurvature hC t).continuousOn

theorem bounded_curvature_on_past_of_bound_at
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientLimitFlow 3)
    (hderivative : ∀ t : ℝ, t < 0 → ∀ x : L.carrier.carrier,
      ∃ dR : ℝ, HasDerivWithinAt
        (fun s => (L.flow.connection s).scalarCurvature x) dR (Iio 0) t ∧ 0 ≤ dR)
    {τ : ℝ} (hτ : τ < 0)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.carrier.carrier,
      |(L.flow.connection τ).curvatureTensorNorm x| ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ≤ τ, ∀ x : L.carrier.carrier,
      |(L.flow.connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := hbound
  refine ⟨27 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro t ht x
  have ht0 : t < 0 := lt_of_le_of_lt ht hτ
  have hnonneg : 0 ≤ (L.flow.connection t).curvatureTensorNorm x := Real.sqrt_nonneg _
  rw [abs_of_nonneg hnonneg]
  have hmono := L.scalarCurvature_monotoneOn_of_derivative_nonnegative hderivative x ht0 hτ ht
  have hscalar := (L.flow.connection τ).scalarCurvature_le_curvatureTensorNorm_sharp x
  have hnorm := (le_abs_self ((L.flow.connection τ).curvatureTensorNorm x)).trans (hbound x)
  have hcompare := L.curvatureTensorNorm_le_scalarCurvature hC t ht0 x
  norm_num at hscalar
  linarith

end PoincareConjecture.AncientLimitFlow
