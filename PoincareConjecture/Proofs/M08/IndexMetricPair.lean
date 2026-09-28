import PoincareConjecture.Proofs.M08.PullbackRegularity
import PoincareConjecture.Proofs.M08.SecondVariationCoefficients
import PoincareConjecture.Proofs.M08.JacobiInitialValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance indexMetricPairDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance indexMetricPairDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance indexMetricPairBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance indexMetricPairBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1200000 in
theorem chartMovingMetric_pair_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    (x : M) (α : ℝ → M) {s : ℝ} (hs : s ∈ Ioo a b)
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (c d : ℝ → EuclideanSpace ℝ (Fin n)) (dc dd : EuclideanSpace ℝ (Fin n))
    (hc : HasDerivAt c dc s) (hd : HasDerivAt d dd s) :
    HasDerivAt
      (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)) (c r) (d r))
      (let z := (s, extChartAt (𝓡 n) x (α s))
       let v := deriv ((extChartAt (𝓡 n) x) ∘ α) s
       let Γ := closedChartConnection F T x (Icc a b) z
       chartActionMetric F T x z (dc + Γ v (c s)) (d s) +
         chartActionMetric F T x z (c s) (dd + Γ v (d s)) +
         4 * s * (F.connection (T - s ^ 2)).ricci (α s)
           (chartFrame x (c s) (α s)) (chartFrame x (d s) (α s))) s := by
  let C := Icc a b
  let U := (extChartAt (𝓡 n) x).target
  let G := chartActionMetric F T x
  let q := (extChartAt (𝓡 n) x) ∘ α
  let v := deriv q s
  let Γ := closedChartConnection F T x C (s, q s)
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hsN : C ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hqmem : q s ∈ U := (extChartAt (𝓡 n) x).map_source
    (by simpa only [extChartAt_source] using hx)
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hG : ContDiffOn ℝ ∞ G (C ×ˢ U) := chartActionMetric_closed_contDiffOn F T x htime
  have hGd : DifferentiableAt ℝ G (s, q s) := ((hG (s, q s) ⟨hsC, hqmem⟩).contDiffAt
    (prod_mem_nhds hsN (hU.mem_nhds hqmem))).differentiableAt (by simp)
  have hqd : DifferentiableAt ℝ q s :=
    (((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hx).mdifferentiableAt
      (by simp)).comp s hα).differentiableAt
  have hgraph : HasDerivAt (fun r : ℝ ↦ (r, q r)) (1, v) s :=
    (hasDerivAt_id s).prodMk hqd.hasDerivAt
  have hGc : HasDerivAt (fun r : ℝ ↦ G (r, q r)) (fderiv ℝ G (s, q s) (1, v)) s := by
    simpa only [Function.comp_def] using
      (hGd.hasFDerivAt.comp_hasDerivAt (l := G)
        (l' := fderiv ℝ G (s, q s)) s hgraph)
  have hcompat := closedChartConnection_spatial_compatibility F T htime hx hsC v (c s) (d s)
  change fderiv ℝ (fun y ↦ G (s, y)) (q s) v (c s) (d s) =
    G (s, q s) (Γ v (c s)) (d s) + G (s, q s) (c s) (Γ v (d s)) at hcompat
  rw [(hasFDerivAt_spatialWithin hU G hG hsC hqmem).fderiv,
    spatialWithinFDeriv_eq_spatialFDeriv hU G hsN hqmem] at hcompat
  change fderiv ℝ G (s, q s) (0, v) (c s) (d s) =
    G (s, q s) (Γ v (c s)) (d s) + G (s, q s) (c s) (Γ v (d s)) at hcompat
  have hcompat' : fderiv ℝ G (s, q s) (1, v) (c s) (d s) =
      G (s, q s) (Γ v (c s)) (d s) + G (s, q s) (c s) (Γ v (d s)) +
        fderiv ℝ G (s, q s) (1, 0) (c s) (d s) := by
    rw [show ((1 : ℝ), v) = (1, (0 : EuclideanSpace ℝ (Fin n))) + (0, v) by simp,
      map_add, add_apply, add_apply, hcompat]
    ring
  have h := chart_pair_moving_covariant_hasDerivAt (fun r ↦ G (r, q r)) Γ
    (fderiv ℝ G (s, q s) (1, 0)) (fderiv ℝ G (s, q s) (1, v)) hGc hc hd hcompat'
  have htimepair : fderiv ℝ G (s, q s) (1, 0) (c s) (d s) =
      4 * s * (F.connection (T - s ^ 2)).ricci (α s)
        (chartFrame x (c s) (α s)) (chartFrame x (d s) (α s)) :=
    chartActionMetric_time_pair_interior F hM04 T (uniqueDiffOn_Icc hab) htime hx hsC hsN
      (c s) (d s)
  rw [htimepair] at h
  exact h

set_option maxHeartbeats 1600000 in
theorem pullback_metric_pair_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y Z : ∀ r, TangentSpace (𝓡 n) (α r))
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (EZ : ParametricAlongCurveExtensionOn (Icc a b) α Z)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (fun r ↦ (F.metric (T - r ^ 2)).inner (α r) (Y r) (Z r))
      ((F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY s) (Z s) +
        (F.metric (T - s ^ 2)).inner (α s) (Y s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Z (Icc a b) EZ s) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s) (Y s) (Z s)) s := by
  let x := α s
  let c := parametricExtension_chartCoordinates EY x
  let d := parametricExtension_chartCoordinates EZ x
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have hsC : s ∈ Icc a b := Ioo_subset_Icc_self hs
  obtain ⟨N, hN, hsN, hNU, hsrc, hc, hY⟩ :=
    exists_parametricExtension_chartCoordinates hU hCU α hα Y EY hsC hx
  obtain ⟨O, hO, hsO, hOU, hsrcO, hd, hZ⟩ :=
    exists_parametricExtension_chartCoordinates hU hCU α hα Z EZ hsC hx
  have hαs := ((hα s (hCU hsC)).contMDiffAt (hU.mem_nhds (hCU hsC))).mdifferentiableAt
    (by simp)
  have hdc : HasDerivAt c (deriv c s) s :=
    (((hc s hsN).contDiffAt (hN.mem_nhds hsN)).differentiableAt (by simp)).hasDerivAt
  have hdd : HasDerivAt d (deriv d s) s :=
    (((hd s hsO).contDiffAt (hO.mem_nhds hsO)).differentiableAt (by simp)).hasDerivAt
  have hpair := chartMovingMetric_pair_hasDerivAt F hM04 T hab htime x α hs hx hαs c d
    (deriv c s) (deriv d s) hdc hdd
  have hDY := pullbackCovariantDerivative_chart_extension F T hab htime hN x α
    (hα.mono hNU) Y EY hsrc hc hY ⟨hsC, hsN⟩
  have hDZ := pullbackCovariantDerivative_chart_extension F T hab htime hO x α
    (hα.mono hOU) Z EZ hsrcO hd hZ ⟨hsC, hsO⟩
  have hnear : ∀ᶠ r in 𝓝 s, r ∈ Icc a b ∩ N ∩ O :=
    inter_mem (inter_mem (Icc_mem_nhds hs.1 hs.2) (hN.mem_nhds hsN)) (hO.mem_nhds hsO)
  have heq : (fun r ↦ (F.metric (T - r ^ 2)).inner (α r) (Y r) (Z r)) =ᶠ[𝓝 s]
      (fun r ↦ chartActionMetric F T x (r, extChartAt (𝓡 n) x (α r)) (c r) (d r)) := by
    filter_upwards [hnear] with r hr
    rw [chartActionMetric_apply F T (hsrc hr.1.2), hY r hr.1, hZ r ⟨hr.1.1, hr.2⟩]
  have hvalue :
      (let z := (s, extChartAt (𝓡 n) x (α s))
       let v := deriv ((extChartAt (𝓡 n) x) ∘ α) s
       let Γ := closedChartConnection F T x (Icc a b) z
       chartActionMetric F T x z (deriv c s + Γ v (c s)) (d s) +
         chartActionMetric F T x z (c s) (deriv d s + Γ v (d s)) +
         4 * s * (F.connection (T - s ^ 2)).ricci (α s)
           (chartFrame x (c s) (α s)) (chartFrame x (d s) (α s))) =
      (F.metric (T - s ^ 2)).inner (α s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY s) (Z s) +
        (F.metric (T - s ^ 2)).inner (α s) (Y s)
          (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Z (Icc a b) EZ s) +
        4 * s * (F.connection (T - s ^ 2)).ricci (α s) (Y s) (Z s) := by
    dsimp only
    rw [chartActionMetric_apply F T hx, chartActionMetric_apply F T hx,
      hY s ⟨hsC, hsN⟩, hZ s ⟨hsC, hsO⟩, hDY, hDZ]
    rfl
  rw [hvalue] at hpair
  exact hpair.congr_of_eventuallyEq heq

theorem extension_metric_pair_contDiffOn {J C : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (htime : ∀ r ∈ C, T - r ^ 2 ∈ J)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α C)
    (Y Z : ∀ r, TangentSpace (𝓡 n) (α r))
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (EZ : ParametricAlongCurveExtensionOn C α Z) :
    ContDiffOn ℝ ∞ (fun r ↦ (F.metric (T - r ^ 2)).inner (α r) (Y r) (Z r)) C := by
  exact (movingMetric_pair_contMDiffOn F (fun r ↦ T - r ^ 2) α Y Z
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn hα
    (parametricExtension_along_contMDiffOn EY hα)
    (parametricExtension_along_contMDiffOn EZ hα) htime).contDiffOn

end PoincareConjecture.M08


