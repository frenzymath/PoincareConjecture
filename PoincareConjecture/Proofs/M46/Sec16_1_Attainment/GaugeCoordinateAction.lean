import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoveryAction
import PoincareConjecture.Proofs.M14.Sec6_2_SquareCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

private noncomputable local instance : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem gaugeCylinderAction_eq_coordinate_integral
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) (j : G.gaugeCover.index)
    (x0 : G.gaugeCover.spatial j) {T a b : ℝ} (hab : a ≤ b)
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (htheta : ContinuousOn theta (Icc a b))
    (hclock : ∀ s ∈ Icc a b, (theta s).val = T - s ^ 2)
    (alpha : ℝ → G.gaugeCover.spatial j) (halpha : ContinuousOn alpha (Icc a b))
    (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b)
    (d : ℝ → EuclideanSpace ℝ (Fin 3))
    (hd : (w : ℝ → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume.restrict (Icc a b)] d) :
    gaugeCylinderAction j theta alpha w = ∫ s in a..b,
      M14.squareMetricCoefficient (G.gaugeCover.spatial j) (G.gaugeCover.metric j).metric
        T x0 (s, (alpha s).val) (d s) (d s) / 2 +
      M14.squarePotentialCoefficient j theta x0 (s, (alpha s).val) := by
  let B := M14.squareMetricCoefficient (G.gaugeCover.spatial j)
    (G.gaugeCover.metric j).metric T x0
  let V := M14.squarePotentialCoefficient j theta x0
  have htime (s : ℝ) (hs : s ∈ Icc a b) :
      T - s ^ 2 ∈ (G.gaugeCover.interval j).domain := by
    rw [← hclock s hs]
    exact (theta s).property
  have hB := (M14.squareMetricCoefficient_contDiffOn (G.gaugeCover.spatial j)
    (G.gaugeCover.metric j).metric (G.gaugeCover.metric j).smooth T x0 htime).continuousOn
  have hgraph : ContinuousOn (fun s => (s, (alpha s).val)) (Icc a b) :=
    continuousOn_id.prodMk (continuous_subtype_val.comp_continuousOn halpha)
  have hBc : ContinuousOn (fun s => B (s, (alpha s).val)) (Icc a b) :=
    hB.comp hgraph (fun _ hs => ⟨hs, (alpha _).property⟩)
  have hkin : IntervalIntegrable (fun s => B (s, (alpha s).val) (w s) (w s) / 2)
      volume a b :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (M08.chart_density_integrable _ (M08.continuousOn_memLp_top_Icc hBc) w)).div_const 2
  have hchart (s : ℝ) :
      (chartAt (EuclideanSpace ℝ (Fin 3)) x0).symm (alpha s).val = alpha s := by
    change (chartAt (EuclideanSpace ℝ (Fin 3)) x0).symm
      ((chartAt (EuclideanSpace ℝ (Fin 3)) x0) (alpha s)) = alpha s
    apply (chartAt (EuclideanSpace ℝ (Fin 3)) x0).left_inv
    rw [(G.gaugeCover.spatial j).chartAt_source_eq_univ]
    exact mem_univ _
  have hVeq (s : ℝ) : V (s, (alpha s).val) = 2 * s ^ 2 *
      horizontalScalarCurvature G.leafwise
        ((G.gaugeCover.cylinder j).toSpacetime (theta s, alpha s)) := by
    simp only [V, M14.squarePotentialCoefficient, hchart]
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hVc : ContinuousOn (fun s => V (s, (alpha s).val)) (Icc a b) := by
    simp only [hVeq]
    have hscalar := H.scalar_smooth.continuous.comp (G.gaugeCover.cylinder j).smooth.continuous
    exact (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (hscalar.comp_continuousOn (htheta.prodMk halpha))
  have heq : gaugeCylinderAction j theta alpha w =
      (∫ s in a..b, B (s, (alpha s).val) (w s) (w s) / 2) +
        ∫ s in a..b, V (s, (alpha s).val) := by
    unfold gaugeCylinderAction
    congr 1
    · apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hab] at hs
      simp only [B, M14.squareMetricCoefficient_apply, hclock s hs]
      ring
    · exact intervalIntegral.integral_congr (fun s _ => (hVeq s).symm)
  rw [heq, ← intervalIntegral.integral_add hkin (hVc.intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hd] with s hs
  rw [hs]

end PoincareConjecture.Proofs.M46
