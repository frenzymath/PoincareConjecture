import PoincareConjecture.Proofs.M08.IndexPairAlgebra
import PoincareConjecture.Proofs.M08.ChartEulerEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance indexContinuityDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance indexContinuityDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance indexContinuityBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance indexContinuityBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem alongField_chartCoordinates_contDiffOn {C : Set ℝ} (x : M) (α : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) C)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContDiffOn ℝ ∞ (fun s ↦
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
        (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s))).2) C := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have h := e.contMDiffOn.comp hY (fun s hs ↦ e.mem_source.mpr (hsrc hs))
  exact ContMDiffOn.contDiffOn (fun s hs ↦ (h s hs).snd)

set_option maxHeartbeats 1600000 in
theorem jacobiPairResidual_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y P DP W : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) (Icc a b))
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (P s)) (Icc a b))
    (hDP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (DP s)) (Icc a b))
    (hW : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (W s)) (Icc a b)) :
    ContDiffOn ℝ ∞ (fun s ↦ jacobiPairResidual F T α (Icc a b) s
      (Y s) (P s) (DP s) (W s)) (Icc a b) := by
  intro s hs
  let x := α s
  let N := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  let C := Icc a b ∩ N
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let coord := fun (H : ∀ r, TangentSpace (𝓡 n) (α r)) (r : ℝ) ↦
    (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r) (H r))).2
  have hN : IsOpen N := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hsN : s ∈ N := ⟨hCU hs, mem_chart_source _ _⟩
  have hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source := fun r hr ↦ hr.2.2
  have hcoord (H : ∀ r, TangentSpace (𝓡 n) (α r))
      (hH : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r) (H r)) (Icc a b)) :
      ContDiffOn ℝ ∞ (coord H) C :=
    alongField_chartCoordinates_contDiffOn x α H (hH.mono inter_subset_left) hsrc
  have hq : ContDiffOn ℝ ∞ ((extChartAt (𝓡 n) x) ∘ α) C :=
    chart_curve_contDiffOn x α (hα.mono (inter_subset_right.trans inter_subset_left)) hsrc
  have hmap : MapsTo (fun r ↦ (r, extChartAt (𝓡 n) x (α r))) C
      (Icc a b ×ˢ (extChartAt (𝓡 n) x).target) := by
    intro r hr
    exact ⟨hr.1, (extChartAt (𝓡 n) x).map_source
      (by simpa only [extChartAt_source] using hsrc hr)⟩
  have hG := (chartActionMetric_closed_contDiffOn F T x htime).comp
    (f := fun r ↦ (r, extChartAt (𝓡 n) x (α r))) (contDiffOn_id.prodMk hq) hmap
  obtain ⟨_, _, hK, hH⟩ := jacobiAlongCoefficients_contDiffOn F hM04 T x α
    (uniqueDiffOn_Icc hab) htime (show C ⊆ Icc a b from inter_subset_left) hU
    (show C ⊆ U from inter_subset_right.trans inter_subset_left) hα hsrc
  have hform := (((hG.clm_apply (hcoord DP hDP)).clm_apply (hcoord W hW)).sub
    ((hK.clm_apply (hcoord Y hY)).clm_apply (hcoord W hW))).add
      ((hH.clm_apply (hcoord P hP)).clm_apply (hcoord W hW))
  have hactual : ContDiffOn ℝ ∞ (fun r ↦ jacobiPairResidual F T α (Icc a b) r
      (Y r) (P r) (DP r) (W r)) C := by
    apply hform.congr
    intro r hr
    have hαr := ((hα r hr.2.1).contMDiffAt (hU.mem_nhds hr.2.1)).mdifferentiableAt (by simp)
    have hid := jacobiPairResidual_chart F hM04 T hab htime x α hr.1 (hsrc hr) hαr
      (coord Y r) (coord P r) (coord DP r) (coord W r)
    simpa only [coord, e, Function.comp_apply, chartFrame_coordinates_at (hsrc hr)] using hid
  exact (contDiffWithinAt_inter (hN.mem_nhds hsN)).mp (hactual s ⟨hs, hsN⟩)

theorem regularizedIndexPairDensity_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y W DY DW : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) (Icc a b))
    (hW : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (W s)) (Icc a b))
    (hDY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (DY s)) (Icc a b))
    (hDW : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (DW s)) (Icc a b)) :
    ContDiffOn ℝ ∞ (fun s ↦ regularizedIndexPairDensity F T α (Icc a b) s
      (Y s) (W s) (DY s) (DW s)) (Icc a b) := by
  have hzero : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (0 : TangentSpace (𝓡 n) (α s))) (Icc a b) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 n))).comp_contMDiffOn (hα.mono hCU)
  have hres := jacobiPairResidual_contDiffOn F hM04 T hab htime hU hCU α hα
    Y (fun _ ↦ 0) (fun _ ↦ 0) W hY hzero hzero hW
  have hpair := movingMetric_pair_contMDiffOn F (fun s ↦ T - s ^ 2) α DY DW
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn (hα.mono hCU) hDY hDW htime
  exact hpair.contDiffOn.sub hres

end PoincareConjecture.M08
