import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCoordinateJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCoordinateSmooth
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCylinderReadout
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators
open Poincare.Analysis.Calculus
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private noncomputable def neckCoefficientEvaluation (a b : Fin 3) :
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis b)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis a))

private theorem norm_neckCoefficientEvaluation_le (a b : Fin 3) :
    ‖neckCoefficientEvaluation a b‖ ≤ 1 := by
  have hb (i : Fin 3) : ‖roundCylinderCoordinateBasis i‖ = 1 := by
    fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro B
  simpa only [neckCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, hb, mul_one, one_mul] using
      B.le_opNorm₂ (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "OrdinaryFlow" => ordinaryChapter11Flow (I := I) (F := F) R

private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem ordinaryChapter11_locally_uniform_neck_coefficientJets
    (p : ℕ → (OrdinaryFlow).point) (hpositive : ∀ k, 0 < (OrdinaryFlow).scalar (p k))
    (hdiverges : Tendsto (fun k => (OrdinaryFlow).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (OrdinaryFlow) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (N : EpsilonNeck (C.limit.flow.metric 0))
    (z₀ : RoundCylinderSpace) (hz₀ : z₀.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (radius : ℝ) (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ∃ V : Set RoundCylinderSpace, V ∈ 𝓝 z₀ ∧
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ V, z.2 ∈ Icc (-radius) radius →
        ∀ s ∈ Icc (-1 : ℝ) 0, ∀ j ≤ m, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
              (generalizedCylinderPullback (C.embedding k) N.coordinate_map s)
              (chartAt E₂ z.1) y a b -
            roundCylinderTensorCoefficient
              (roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map)
              (chartAt E₂ z.1) y a b) (0, z.2)‖ < rho := by
  classical
  let a : C.limit.sliceCarrier.carrier := N.coordinate_map z₀
  let c := extChartAt (𝓡 3) a
  obtain ⟨H, hH, haH, hHt⟩ := exists_compact_subset
    (isOpen_extChartAt_target (I := 𝓡 3) a) (mem_extChartAt_target (I := 𝓡 3) a)
  obtain ⟨D, hD, hDnear⟩ := N.exists_local_parametrization_jet_bound
    a z₀.1 z₀.2 radius (m + 1) hz₀ (mem_extChartAt_source a)
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound
      (E := RoundCylinderCoordinates) (F := E₃) (G := ℝ) j hD
  let B₀ : ℝ := ∑ j : Fin (m + 1), B j
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg (fun j _ => hB j)
  let eta := rho / (B₀ + 1)
  have heta : 0 < eta := div_pos hrho (by linarith)
  have hsmall : B₀ * eta < rho := by
    have hscale : (B₀ + 1) * eta = rho := by
      dsimp [eta]
      field_simp
    nlinarith
  have hmap : ContinuousAt N.coordinate_map z₀ :=
    (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz₀⟩)).continuousAt
  have hchart : ∀ᶠ z in 𝓝 z₀, N.coordinate_map z ∈ c.source :=
    hmap.tendsto.eventually ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a))
  have hHnear : ∀ᶠ z in 𝓝 z₀, c (N.coordinate_map z) ∈ H :=
    ((continuousAt_extChartAt a).comp hmap).tendsto.eventually
      (mem_interior_iff_mem_nhds.mp haH)
  have haxial : ∀ᶠ z : RoundCylinderSpace in 𝓝 z₀,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hz₀)
  let V : Set RoundCylinderSpace := {z | N.coordinate_map z ∈ c.source ∧
    c (N.coordinate_map z) ∈ H ∧ z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
    (z.2 ∈ Icc (-radius) radius → ∀ j ≤ m + 1,
      ‖iteratedFDeriv ℝ j (fun y : RoundCylinderCoordinates =>
        c (N.coordinate_map ((chartAt E₂ z.1).symm y.1, y.2))) (0, z.2)‖ ≤ D)}
  have hV : V ∈ 𝓝 z₀ := by
    filter_upwards [hchart, hHnear, haxial, hDnear] with z hz₁ hz₂ hz₃ hz₄
    exact ⟨hz₁, hz₂, hz₃, hz₄⟩
  have hcompact : IsCompact (c.symm '' H) :=
    hH.image_of_continuousOn ((continuousOn_extChartAt_symm a).mono hHt)
  obtain ⟨j₀, hj₀⟩ := C.exists_exhaustion_superset hcompact
  have hdom : Icc (-1 : ℝ) 0 ×ˢ H ⊆ {z | z ∈ blowupMetricChartDomain C.limit a ∧
      c.symm z.2 ∈ C.exhaustion.space j₀} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    exact ⟨⟨hJI hs, hHt hy⟩, hj₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨k₀, hjk₀, hk₀⟩ := ordinaryChapter11_uniform_bilinear_metricJets
    R p hpositive hdiverges C hJ a j₀ m (Icc (-1 : ℝ) 0 ×ˢ H)
      (isCompact_Icc.prod hH) hdom eta heta
  refine ⟨V, hV, ?_⟩
  filter_upwards [eventually_ge_atTop k₀] with k hk z hz hzradius s hs j hj i l
  rcases hz with ⟨hzchart, hzH, hzaxis, hzjets⟩
  let φ : RoundCylinderCoordinates → C.limit.sliceCarrier.carrier := fun y =>
    N.coordinate_map ((chartAt E₂ z.1).symm y.1, y.2)
  let f : RoundCylinderCoordinates → E₃ := c ∘ φ
  let x : RoundCylinderCoordinates := (0, z.2)
  let T : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    blowupCoordinateBilinear (C.embedding k) a s y - limitCoordinateBilinear C.limit a s y
  have hφx : φ x = N.coordinate_map z := by simp only [φ, x, sphere_chart_symm_zero]
  have hfx : f x = c (N.coordinate_map z) := congrArg c hφx
  have hsource := (hk₀ k hk).1
    (show (s, c (N.coordinate_map z)) ∈ Icc (-1 : ℝ) 0 ×ˢ H from ⟨hs, hzH⟩)
  have hcapture : c.symm (f x) ∈ C.exhaustion.space k := by
    rw [hfx]
    exact C.exhaustion.space_increasing (hjk₀.trans hk) (hj₀ ⟨_, hzH, rfl⟩)
  have hN : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map
      ((chartAt E₂ z.1).symm x.1, x.2) := by
    simpa only [x, sphere_chart_symm_zero] using
      N.coordinate_map_smooth.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzaxis⟩)
  have hφ : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ φ x :=
    hN.comp x (cylinderChart_symm_smooth z.1 x)
  have hchartx : φ x ∈ c.source := by rw [hφx]; exact hzchart
  have hf : ContDiffAt ℝ ∞ f x := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_extChartAt (I := 𝓡 3) (x := a) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source a).mem_nhds hchartx)).comp x hφ)
  have hT : ContDiffAt ℝ ∞ T (f x) :=
    (ordinaryChapter11CoordinateBilinear_contDiffAt R (C.embedding k)
      (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected hsource.1 a
      ⟨by rw [hfx]; exact hsource.2, hcapture⟩).sub
      (limitCoordinateBilinear_contDiffAt C.limit a (hJI hs)
        (by rw [hfx]; exact hHt hzH))
  have hTjet (r : ℕ) (hr : r ≤ j) : ‖iteratedFDeriv ℝ r T (f x)‖ ≤ eta := by
    rw [hfx]
    exact ((hk₀ k hk).2 (s, c (N.coordinate_map z)) ⟨hs, hzH⟩ r (hr.trans hj)).le
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hpullback := hbound j' f T x hf hT
    (fun r hr => hzjets hzradius r (hr.trans (Nat.add_le_add_right hj 1))) eta heta.le hTjet
  let P := fun y => (T (f y)).bilinearComp (fderiv ℝ f y) (fderiv ℝ f y)
  have hP : ContDiffAt ℝ ∞ P x := hf.bilinearPullback hT
  have heq : (fun y => roundCylinderTensorCoefficient
      (generalizedCylinderPullback (C.embedding k) N.coordinate_map s) (chartAt E₂ z.1) y i l -
      roundCylinderTensorCoefficient
        (roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map)
        (chartAt E₂ z.1) y i l) =ᶠ[𝓝 x] (neckCoefficientEvaluation i l) ∘ P := by
    have hnear := hφ.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source a).mem_nhds hchartx)
    have hnearaxial : ∀ᶠ y : RoundCylinderCoordinates in 𝓝 x,
        y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hzaxis)
    filter_upwards [hnear, hnearaxial] with y hy hyaxis
    exact cylinder_coefficient_difference_fixed_chart (C.embedding k) N.coordinate_map
      z.1 a hsource.1 y ((N.coordinate_map_smooth.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hyaxis⟩)).mdifferentiableAt
          (by simp)) hy i l
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  have hpost := (neckCoefficientEvaluation i l).norm_iteratedFDeriv_comp_left
    hP (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j P x‖ := hpost.trans
      ((mul_le_mul_of_nonneg_right (norm_neckCoefficientEvaluation_le i l)
        (norm_nonneg _)).trans_eq (one_mul _))
    _ ≤ B j' * eta := hpullback
    _ ≤ B₀ * eta := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun r _ => hB r) (Finset.mem_univ j')) heta.le
    _ < rho := hsmall

end PoincareConjecture.M34
