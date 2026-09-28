import PoincareConjecture.Proofs.M08.ChartConnectionVariation
import PoincareConjecture.Proofs.M08.ChartCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance connectionTimeIdentityDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance connectionTimeIdentityDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance connectionTimeIdentityBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance connectionTimeIdentityBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance connectionTimeIdentityTrilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance connectionTimeIdentityTrilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem chartActionMetric_timeWithin {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target) :
    timeWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) (s, q) =
      (4 * s) • chartRicciForm hM04 (F.connection (T - s ^ 2)) x q := by
  let e := extChartAt (𝓡 n) x
  have hy : e.symm q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    simpa only [e, extChartAt_source] using e.map_target hq
  ext v w
  have hG := hasDerivWithinAt_timeWithin (chartActionMetric F T x)
    (chartActionMetric_closed_contDiffOn F T x htime) hs hq
  have hpair := (hG.clm_apply (hasDerivWithinAt_const s C v)).clm_apply
    (hasDerivWithinAt_const s C w)
  have hevol := chartActionMetric_closed_time_derivative F T htime hy hs v w
  have heq : extChartAt (𝓡 n) x (e.symm q) = q := e.right_inv hq
  rw [heq] at hevol
  have h := (hpair.derivWithin (hC s hs)).symm.trans (hevol.derivWithin (hC s hs))
  simpa only [map_zero, add_zero, smul_apply, smul_eq_mul, chartRicciForm_apply] using h

theorem chartActionMetric_mixedWithin {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (hcl : (s, q) ∈ closure (interior (C ×ˢ (extChartAt (𝓡 n) x).target)))
    (v : EuclideanSpace ℝ (Fin n)) :
    timeWithinFDeriv C (extChartAt (𝓡 n) x).target
        (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x)) (s, q) v =
      (4 * s) • fderiv ℝ (chartRicciForm hM04 (F.connection (T - s ^ 2)) x) q v := by
  let U := (extChartAt (𝓡 n) x).target
  let G := chartActionMetric F T x
  let H := timeWithinFDeriv C U G
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hG := chartActionMetric_closed_contDiffOn F T x htime
  have hH := timeWithinFDeriv_contDiffOn hC hU G hG
  rw [closed_time_spatial_commute hC hU G hG ⟨hs, hq⟩ hcl v]
  have hd := hasFDerivAt_spatialWithin hU H hH hs hq
  have hR := (((chartRicciForm_contDiffOn hM04 (F.connection (T - s ^ 2)) x) q hq).contDiffAt
    (hU.mem_nhds hq)).differentiableAt (by simp)
  have hscaled := hR.hasFDerivAt.const_smul (4 * s)
  have hscaled' : HasFDerivAt (fun r ↦ H (s, r))
      ((4 * s) • fderiv ℝ (chartRicciForm hM04 (F.connection (T - s ^ 2)) x) q) q := by
    apply hscaled.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hq] with r hr
    exact chartActionMetric_timeWithin F hM04 T x hC htime hs hr
  have heq := hd.unique hscaled'
  exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A v) heq

set_option maxHeartbeats 4000000 in
theorem closedChartChristoffel_time_pair {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) (hC : UniqueDiffOn ℝ C)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) {s : ℝ} (hs : s ∈ C)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (hcl : (s, q) ∈ closure (interior (C ×ˢ (extChartAt (𝓡 n) x).target)))
    (v w z : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, q)
        (timeWithinFDeriv C (extChartAt (𝓡 n) x).target
          (fun r ↦ closedChartChristoffel F T x C r v w) (s, q)) z =
      2 * s * (fderiv ℝ (chartRicciForm hM04 (F.connection (T - s ^ 2)) x) q v w z +
        fderiv ℝ (chartRicciForm hM04 (F.connection (T - s ^ 2)) x) q w v z -
        fderiv ℝ (chartRicciForm hM04 (F.connection (T - s ^ 2)) x) q z v w -
        2 * chartRicciForm hM04 (F.connection (T - s ^ 2)) x q
          (closedChartChristoffel F T x C (s, q) v w) z) := by
  let U := (extChartAt (𝓡 n) x).target
  let G := chartActionMetric F T x
  let DG := spatialWithinFDeriv C U G
  let Γ := fun r ↦ closedChartChristoffel F T x C r v w
  let B := chartRicciForm hM04 (F.connection (T - s ^ 2)) x
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hG := chartActionMetric_closed_contDiffOn F T x htime
  have hDG := spatialWithinFDeriv_contDiffOn hC hU G hG
  have hΓ : ContDiffOn ℝ ∞ Γ (C ×ˢ U) := by
    let k : ℝ × EuclideanSpace ℝ (Fin n) →
        (ℝ × EuclideanSpace ℝ (Fin n)) ×
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := fun r ↦ (r, (v, w))
    have hk : ContDiff ℝ ∞ k := contDiff_id.prodMk contDiff_const
    have hm : MapsTo k (C ×ˢ U) ((C ×ˢ U) ×ˢ univ) :=
      fun r hr ↦ ⟨hr, mem_univ (v, w)⟩
    have h := ContDiffOn.comp (closedChartChristoffel_contDiffOn F T x hC htime)
      hk.contDiffOn hm
    change ContDiffOn ℝ ∞ Γ (C ×ˢ U) at h
    exact h
  have hdG := hasDerivWithinAt_timeWithin G hG hs hq
  have hdΓ := hasDerivWithinAt_timeWithin Γ hΓ hs hq
  have hp := (hdG.clm_apply hdΓ).clm_apply (hasDerivWithinAt_const s C z)
  have hDGtime (a b c : EuclideanSpace ℝ (Fin n)) :
      HasDerivWithinAt (fun r ↦ DG (r, q) a b c)
        (4 * s * fderiv ℝ B q a b c) C s := by
    have h := (((hasDerivWithinAt_timeWithin DG hDG hs hq).clm_apply
      (hasDerivWithinAt_const s C a)).clm_apply
        (hasDerivWithinAt_const s C b)).clm_apply (hasDerivWithinAt_const s C c)
    have heq := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A b c)
      (chartActionMetric_mixedWithin F hM04 T x hC htime hs hq hcl a)
    simp only [smul_apply, smul_eq_mul] at heq
    have h' : HasDerivWithinAt (fun r ↦ DG (r, q) a b c)
        (timeWithinFDeriv C U DG (s, q) a b c) C s := by
      simpa only [map_zero, add_zero] using h
    rwa [heq] at h'
  have hSigma := ((hDGtime v w z).add (hDGtime w v z) |>.sub (hDGtime z v w)).div_const 2
  have hp' : HasDerivWithinAt
      (fun r ↦ (DG (r, q) v w z + DG (r, q) w v z - DG (r, q) z v w) / 2)
      (G (s, q) (timeWithinFDeriv C U Γ (s, q)) z +
        timeWithinFDeriv C U G (s, q) (Γ (s, q)) z) C s := by
    have hp₀ : HasDerivWithinAt (fun r ↦ G (r, q) (Γ (r, q)) z)
        (G (s, q) (timeWithinFDeriv C U Γ (s, q)) z +
          timeWithinFDeriv C U G (s, q) (Γ (s, q)) z) C s := by
      simpa only [map_zero, add_zero, zero_add, add_apply, add_comm] using hp
    apply hp₀.congr_of_mem _ hs
    intro r hr
    exact (closedChartChristoffel_pair F T x C hq v w z).trans
      (chartChristoffelCovector_apply _ v w z) |>.symm
  have heq := (hp'.derivWithin (hC s hs)).symm.trans (hSigma.derivWithin (hC s hs))
  have htG := chartActionMetric_timeWithin F hM04 T x hC htime hs hq
  change timeWithinFDeriv C U G (s, q) = (4 * s) • B q at htG
  rw [htG] at heq
  simp only [smul_apply, smul_eq_mul] at heq
  change G (s, q) (timeWithinFDeriv C U Γ (s, q)) z = _
  dsimp only [B, Γ, G] at heq ⊢
  linarith

theorem chartRicciForm_symm (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (q v w : EuclideanSpace ℝ (Fin n)) :
    chartRicciForm hM04 D x q v w = chartRicciForm hM04 D x q w v :=
  ((hM04.tensor_calculus n M g D).2.2.2.1 _ _ _ 0 0).2.2.2

theorem chartRicciForm_fderiv_symm (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    {q : EuclideanSpace ℝ (Fin n)} (hq : q ∈ (extChartAt (𝓡 n) x).target)
    (v w z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (chartRicciForm hM04 D x) q v w z =
      fderiv ℝ (chartRicciForm hM04 D x) q v z w := by
  let B := chartRicciForm hM04 D x
  have hB : DifferentiableAt ℝ B q :=
    (((chartRicciForm_contDiffOn hM04 D x) q hq).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds hq)).differentiableAt (by simp)
  have hwz := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const w q)).clm_apply
    (hasFDerivAt_const z q)
  have hzw := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const z q)).clm_apply
    (hasFDerivAt_const w q)
  have hsym : (fun r ↦ B r w z) = fun r ↦ B r z w :=
    funext (fun r ↦ chartRicciForm_symm hM04 D x r w z)
  rw [hsym] at hwz
  have h := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ A v) (hwz.unique hzw)
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, add_zero] using h

theorem ricciDerivativePairing_chart_symm {J C : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C) (v w z : EuclideanSpace ℝ (Fin n)) :
    ricciDerivativePairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) =
      ricciDerivativePairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x z y) (chartFrame x w y) := by
  have hq : extChartAt (𝓡 n) x y ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hy)
  rw [ricciDerivativePairing_chart F hM04 T htime hy hs,
    ricciDerivativePairing_chart F hM04 T htime hy hs,
    chartRicciForm_fderiv_symm hM04 _ _ hq v w z,
    chartRicciForm_symm hM04 _ _ _ _ z,
    chartRicciForm_symm hM04 _ _ _ w _]
  ring

set_option maxHeartbeats 1000000 in
theorem closedChartChristoffel_time_eq_connectionVariation {J C : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T : ℝ) (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C)
    (hcl : (s, extChartAt (𝓡 n) x y) ∈
      closure (interior (C ×ˢ (extChartAt (𝓡 n) x).target)))
    (v w z : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (timeWithinFDeriv C (extChartAt (𝓡 n) x).target
          (fun r ↦ closedChartChristoffel F T x C r v w) (s, extChartAt (𝓡 n) x y)) z =
      2 * s * backwardConnectionVariationPairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) := by
  have hq : extChartAt (𝓡 n) x y ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hy)
  rw [closedChartChristoffel_time_pair F hM04 T x hC htime hs hq hcl,
    backwardConnectionVariationPairing,
    ricciDerivativePairing_chart F hM04 T htime hy hs,
    ricciDerivativePairing_chart F hM04 T htime hy hs,
    ricciDerivativePairing_chart F hM04 T htime hy hs]
  rw [closedChartChristoffel_symm F T htime hy hs w v,
    closedChartChristoffel_symm F T htime hy hs z v,
    closedChartChristoffel_symm F T htime hy hs z w,
    chartRicciForm_symm hM04 _ _ _
      (closedChartChristoffel F T x C (s, extChartAt (𝓡 n) x y) v z) w]
  ring

theorem weighted_ricciDerivativePairing_chart {J C : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T : ℝ) (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ C)
    (hcl : (s, extChartAt (𝓡 n) x y) ∈
      closure (interior (C ×ˢ (extChartAt (𝓡 n) x).target)))
    (v w z : EuclideanSpace ℝ (Fin n)) :
    4 * s * ricciDerivativePairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (timeWithinFDeriv C (extChartAt (𝓡 n) x).target
          (fun r ↦ closedChartChristoffel F T x C r v w) (s, extChartAt (𝓡 n) x y)) z +
      chartActionMetric F T x (s, extChartAt (𝓡 n) x y)
        (timeWithinFDeriv C (extChartAt (𝓡 n) x).target
          (fun r ↦ closedChartChristoffel F T x C r v z) (s, extChartAt (𝓡 n) x y)) w := by
  rw [closedChartChristoffel_time_eq_connectionVariation F hM04 T hC htime hy hs hcl,
    closedChartChristoffel_time_eq_connectionVariation F hM04 T hC htime hy hs hcl]
  unfold backwardConnectionVariationPairing
  rw [ricciDerivativePairing_chart_symm F hM04 T htime hy hs w v z,
    ricciDerivativePairing_chart_symm F hM04 T htime hy hs z v w,
    ricciDerivativePairing_chart_symm F hM04 T htime hy hs v z w]
  ring

end PoincareConjecture.M08
