import PoincareConjecture.Proofs.M08.SecondVariationCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.M08

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance secondVariationDensityDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationDensityDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationDensityBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationDensityBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationDensityEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationDensityEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationDensityConnectionGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationDensityConnectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

def curveCoordinateCovariantDerivative (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (q W : ℝ → E) (r : ℝ) : E := deriv W r + Γ (q r) (deriv q r) (W r)

theorem curveCoordinateCovariantDerivative_contDiffOn {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (Γ : E → E →L[ℝ] E →L[ℝ] E) (q W : ℝ → E)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hq : ContDiffOn ℝ ∞ q I)
    (hW : ContDiffOn ℝ ∞ W I) (hmap : MapsTo q I U) :
    ContDiffOn ℝ ∞ (curveCoordinateCovariantDerivative Γ q W) I :=
  (hW.deriv_of_isOpen hI (m := ∞) (by simp)).add
    (((hΓ.comp hq hmap).clm_apply (hq.deriv_of_isOpen hI (m := ∞) (by simp))).clm_apply hW)

theorem chart_density_first_covariant_hasDerivAt
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (P : E → ℝ)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (DP : E →L[ℝ] ℝ)
    {q A : ℝ → E} {u : ℝ} {y a : E}
    (hG : HasFDerivAt G DG (q u)) (hP : HasFDerivAt P DP (q u))
    (hq : HasDerivAt q y u) (hA : HasDerivAt A a u)
    (hsym : ∀ v w : E, G (q u) v w = G (q u) w v)
    (hcompat : DG y (A u) (A u) =
      G (q u) (Γ y (A u)) (A u) + G (q u) (A u) (Γ y (A u))) :
    HasDerivAt (fun r ↦ G (q r) (A r) (A r) / 2 + P (q r))
      (G (q u) (a + Γ y (A u)) (A u) + DP y) u := by
  have h := chart_density_hasDerivAt G P DG DP hG hP hq hA hsym
  have hc := hcompat
  rw [hsym (A u) (Γ y (A u))] at hc
  convert h using 1 <;> try rfl
  simp only [map_add, add_apply]
  rw [hsym (A u) a]
  linarith

set_option maxHeartbeats 1600000 in
theorem chart_density_second_covariant_hasDerivAt {I : Set ℝ} {U : Set E}
    (hI : IsOpen I) (hU : IsOpen U)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (P : E → ℝ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (q A : ℝ → E)
    (hG : ContDiffOn ℝ ∞ G U) (hP : ContDiffOn ℝ ∞ P U)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hq : ContDiffOn ℝ ∞ q I)
    (hA : ContDiffOn ℝ ∞ A I) (hmap : MapsTo q I U)
    (hsym : ∀ x ∈ U, ∀ v w : E, G x v w = G x w v)
    (hcompat : ∀ x ∈ U, ∀ y v w : E,
      fderiv ℝ G x y v w = G x (Γ x y v) w + G x v (Γ x y w))
    {u : ℝ} (hu : u ∈ I) :
    HasDerivAt (fun r ↦ deriv (fun v ↦ G (q v) (A v) (A v) / 2 + P (q v)) r)
      (G (q u) (curveCoordinateCovariantDerivative Γ q
          (curveCoordinateCovariantDerivative Γ q A) u) (A u) +
        G (q u) (curveCoordinateCovariantDerivative Γ q A u)
          (curveCoordinateCovariantDerivative Γ q A u) +
        fderiv ℝ (fderiv ℝ P) (q u) (deriv q u) (deriv q u) -
        fderiv ℝ P (q u) (Γ (q u) (deriv q u) (deriv q u)) +
        fderiv ℝ P (q u) (curveCoordinateCovariantDerivative Γ q (deriv q) u)) u := by
  let L := fun r ↦ G (q r) (A r) (A r) / 2 + P (q r)
  let B := curveCoordinateCovariantDerivative Γ q A
  let Y := deriv q
  have hB : ContDiffOn ℝ ∞ B I :=
    curveCoordinateCovariantDerivative_contDiffOn hI Γ q A hΓ hq hA hmap
  have hY : ContDiffOn ℝ ∞ Y I := hq.deriv_of_isOpen hI (m := ∞) (by simp)
  have hfirst (r : ℝ) (hr : r ∈ I) :
      deriv L r = G (q r) (B r) (A r) + fderiv ℝ P (q r) (Y r) := by
    have hGr := ((hG (q r) (hmap hr)).contDiffAt (hU.mem_nhds (hmap hr))).differentiableAt
      (by simp)
    have hPr := ((hP (q r) (hmap hr)).contDiffAt (hU.mem_nhds (hmap hr))).differentiableAt
      (by simp)
    have hqr := ((hq r hr).contDiffAt (hI.mem_nhds hr)).differentiableAt (by simp)
    have hAr := ((hA r hr).contDiffAt (hI.mem_nhds hr)).differentiableAt (by simp)
    exact (chart_density_first_covariant_hasDerivAt G P (Γ (q r)) _ _
      hGr.hasFDerivAt hPr.hasFDerivAt hqr.hasDerivAt hAr.hasDerivAt
      (hsym (q r) (hmap hr)) (hcompat (q r) (hmap hr) _ _ _)).deriv
  have hqu := ((hq u hu).contDiffAt (hI.mem_nhds hu)).differentiableAt (by simp)
  have hAu := ((hA u hu).contDiffAt (hI.mem_nhds hu)).differentiableAt (by simp)
  have hBu := ((hB u hu).contDiffAt (hI.mem_nhds hu)).differentiableAt (by simp)
  have hYu := ((hY u hu).contDiffAt (hI.mem_nhds hu)).differentiableAt (by simp)
  have hGu := ((hG (q u) (hmap hu)).contDiffAt (hU.mem_nhds (hmap hu))).differentiableAt
    (by simp)
  have hPu := (hP (q u) (hmap hu)).contDiffAt (hU.mem_nhds (hmap hu))
  have hpair := chart_pair_covariant_hasDerivAt G (Γ (q u)) _ hGu.hasFDerivAt
    hqu.hasDerivAt hBu.hasDerivAt hAu.hasDerivAt (hcompat (q u) (hmap hu) _ _ _)
  change HasDerivAt (fun r ↦ G (q r) (B r) (A r))
    (G (q u) (curveCoordinateCovariantDerivative Γ q B u) (A u) + G (q u) (B u) (B u)) u
    at hpair
  have hP₂ := ((hPu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hpot := (hP₂.comp_hasDerivAt u hqu.hasDerivAt).clm_apply hYu.hasDerivAt
  have hsum := hpair.add hpot
  have hactual := hsum.congr_of_eventuallyEq (show
      (fun r ↦ deriv L r) =ᶠ[𝓝 u]
        (fun r ↦ G (q r) (B r) (A r) + fderiv ℝ P (q r) (Y r)) from by
    filter_upwards [hI.mem_nhds hu] with r hr
    exact hfirst r hr)
  convert hactual using 1 <;> try rfl
  dsimp only [curveCoordinateCovariantDerivative, B, Y, Function.comp_def]
  simp only [map_add, add_apply]
  ring

end PoincareConjecture.M08
