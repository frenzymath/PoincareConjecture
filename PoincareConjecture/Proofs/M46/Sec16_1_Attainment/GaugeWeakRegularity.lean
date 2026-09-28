import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeCoordinateAction
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.WeakSmoothness
import PoincareConjecture.Proofs.M08.ClosedChartCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

set_option maxHeartbeats 800000 in




theorem gauge_cylinder_minimum_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) (j : G.gaugeCover.index)
    (x0 : G.gaugeCover.spatial j) {T a b : ℝ} (hab : a < b)
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (htheta : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ theta (Icc a b))
    (hclock : ∀ s ∈ Icc a b, (theta s).val = T - s ^ 2)
    (alpha : ℝ → G.gaugeCover.spatial j) (halpha : ContinuousOn alpha (Icc a b))
    (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b)
    (hprimitive : ∀ s ∈ Icc a b, (alpha s).val = (alpha a).val + ∫ r in a..s, w r)
    (hmin : ∀ beta : ℝ → G.gaugeCover.spatial j, ContinuousOn beta (Icc a b) →
      beta a = alpha a → beta b = alpha b →
      ∀ v : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b,
      (∀ s ∈ Icc a b, (beta s).val = (beta a).val + ∫ r in a..s, v r) →
      gaugeCylinderAction j theta alpha w ≤ gaugeCylinderAction j theta beta v) :
    ContDiffOn ℝ ∞ (fun s => (alpha s).val) (Icc a b) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let B := M14.squareMetricCoefficient (G.gaugeCover.spatial j)
    (G.gaugeCover.metric j).metric T x0
  let V := M14.squarePotentialCoefficient j theta x0
  let S : Set E := G.gaugeCover.spatial j
  have hS : IsOpen S := (G.gaugeCover.spatial j).isOpen
  have htime (s : ℝ) (hs : s ∈ Icc a b) :
      T - s ^ 2 ∈ (G.gaugeCover.interval j).domain := by
    rw [← hclock s hs]
    exact (theta s).property
  have hB := M14.squareMetricCoefficient_contDiffOn (G.gaugeCover.spatial j)
    (G.gaugeCover.metric j).metric (G.gaugeCover.metric j).smooth T x0 htime
  have hV := M14.squarePotentialCoefficient_contDiffOn j theta x0 hM12 htheta
  let DB := M08.spatialWithinFDeriv (Icc a b) S B
  let DV := M08.spatialWithinFDeriv (Icc a b) S V
  have hDB := M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hS B hB
  have hDV := M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hS V hV
  have hsrc : MapsTo alpha (Icc a b) (chartAt E x0).source := by
    rw [(G.gaugeCover.spatial j).chartAt_source_eq_univ]
    exact mapsTo_univ _ _
  have hcoord (z : G.gaugeCover.spatial j) : extChartAt (𝓡 3) x0 z = z.val := by
    rw [extChartAt_coe]
    rfl
  have hsym (z : ℝ × E) (hz : z ∈ Icc a b ×ˢ S) (v v' : E) : B z v v' = B z v' v := by
    have hleft := M14.squareMetricCoefficient_apply (G.gaugeCover.spatial j)
      (G.gaugeCover.metric j).metric T x0 ⟨z.2, hz.2⟩ z.1 v v'
    have hright := M14.squareMetricCoefficient_apply (G.gaugeCover.spatial j)
      (G.gaugeCover.metric j).metric T x0 ⟨z.2, hz.2⟩ z.1 v' v
    exact hleft.trans ((((G.gaugeCover.metric j).metric (T - z.1 ^ 2)).symm _ v v').trans
      hright.symm)
  apply weak_quadratic_minimum_smooth hab hS B V DB DV hB hV.continuousOn hDB hDV
    (fun z hz => M08.hasFDerivAt_spatialWithin hS B hB hz.1 hz.2)
    (fun z hz => M08.hasFDerivAt_spatialWithin hS V hV hz.1 hz.2)
    hsym (fun z hz v hv =>
      M14.squareMetricCoefficient_pos _ _ T x0 z.1 hz.2 v hv)
    (fun s => (alpha s).val) (continuous_subtype_val.comp_continuousOn halpha)
    (fun s _ => (alpha s).property) w hprimitive
  · intro eta heta hsupp
    have hetaA : eta a = 0 := image_eq_zero_of_notMem_tsupport
      (fun ha => (lt_irrefl a) (hsupp ha).1)
    have hetaB : eta b = 0 := image_eq_zero_of_notMem_tsupport
      (fun hb => (lt_irrefl b) (hsupp hb).2)
    have hnu : ContinuousOn (deriv eta) (Icc a b) :=
      (heta.continuous_deriv (by simp)).continuousOn
    have hnuLp : MemLp (deriv eta) 2 (volume.restrict (Icc a b)) :=
      (M08.continuousOn_memLp_top_Icc hnu).mono_exponent le_top
    obtain ⟨K, _, hKt, _, delta, hdelta, _, hshift⟩ :=
      M08.exists_chart_affine_buffer x0 alpha halpha hsrc eta heta.continuous.continuousOn
    let f (e : ℝ) := ∫ s in a..b,
      B (s, (alpha s).val + e • eta s) (w s + e • deriv eta s) (w s + e • deriv eta s) / 2 +
        V (s, (alpha s).val + e • eta s)
    have hbase : gaugeCylinderAction j theta alpha w = f 0 := by
      simpa only [f, zero_smul, add_zero] using gaugeCylinderAction_eq_coordinate_integral
        hM12 j x0 hab.le theta htheta.continuousOn hclock alpha halpha w w EventuallyEq.rfl
    have hn : Ioo (-delta) delta ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (neg_lt_zero.mpr hdelta) hdelta
    filter_upwards [hn] with e he
    have htarget : MapsTo (fun s => extChartAt (𝓡 3) x0 (alpha s) + e • eta s)
        (Icc a b) (extChartAt (𝓡 3) x0).target :=
      fun _ hs => hKt (hshift e (abs_lt.mpr he) hs)
    obtain ⟨beta, v, hbeta, hleft, hright, _, _, hv, hbetaCoord, hbetaPrimitive⟩ :=
      M08.chart_affine_competitor hab.le x0 alpha halpha hsrc w
        (by simpa only [hcoord] using hprimitive) eta (deriv eta) heta.continuous.continuousOn
        (fun s _ => ((heta.differentiable (by simp)) s).hasDerivAt)
        hnuLp hetaA hetaB e htarget
    have haction : gaugeCylinderAction j theta beta v = f e := by
      rw [gaugeCylinderAction_eq_coordinate_integral hM12 j x0 hab.le theta
        htheta.continuousOn hclock beta hbeta v (fun s => w s + e • deriv eta s) hv]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hab.le] at hs
      have hbc := hbetaCoord s hs
      simp only [hcoord] at hbc
      simp only [hbc, B, V]
    change f 0 ≤ f e
    rw [← hbase, ← haction]
    apply hmin beta hbeta hleft hright v
    simpa only [hcoord] using hbetaPrimitive

end PoincareConjecture.Proofs.M46
