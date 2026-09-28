import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.ParametrizationJets
import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.CylinderReadout
import PoincareConjecture.Proofs.M32.Mathlib.BilinearPullbackJets
import PoincareConjecture.Proofs.M32.Claim11_34.Noncompact
import Mathlib.Tactic.FinCases

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

local instance : NormedAddCommGroup
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable def cylinderErrorEvaluation (a b : Fin 3) :
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis b)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis a))

private theorem norm_cylinderErrorEvaluation_le (a b : Fin 3) :
    ‖cylinderErrorEvaluation a b‖ ≤ 1 := by
  have hb (i : Fin 3) : ‖roundCylinderCoordinateBasis i‖ = 1 := by
    fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro B
  simpa only [cylinderErrorEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, hb, mul_one, one_mul] using
      B.le_opNorm₂ (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 12 in
private theorem bilinearPullback_contDiffAt
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] H} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hB : ContDiffAt ℝ ∞ B (f x)) :
    ContDiffAt ℝ ∞ (fun y => (B (f y)).bilinearComp
      (fderiv ℝ f y) (fderiv ℝ f y)) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have h₁ := (hB.comp x hf).clm_comp hd
  let A := (ContinuousLinearMap.flipₗᵢ ℝ E F H).toContinuousLinearEquiv.toContinuousLinearMap
  let D := (ContinuousLinearMap.flipₗᵢ ℝ E E H).toContinuousLinearEquiv.toContinuousLinearMap
  have h₂ := A.contDiff.contDiffAt.comp x h₁
  have h₃ := h₂.clm_comp hd
  exact D.contDiff.contDiffAt.comp x h₃

private theorem captured_cylinderCoefficient_contDiffAt
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I U) (hU : IsOpen U)
    (Phi : RoundCylinderSpace → L.sliceCarrier.carrier)
    (hPhi : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Phi)
    {s : ℝ} (hs : s ∈ I) (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (hp : Phi ((chartAt E₂ q).symm p.1, p.2) ∈ U) (a b : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (generalizedCylinderPullback e Phi s) (chartAt E₂ q) y a b) p := by
  let g := F.metric (origin + s / scale)
  let ψ := (e.forward s hs) ∘ Phi
  let θ := fun y : RoundCylinderCoordinates => ((chartAt E₂ q).symm y.1, y.2)
  have hψ (z : RoundCylinderSpace) (hz : Phi z ∈ U) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ ψ z :=
    ((e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hz)).comp z (hPhi z)
  have hmap : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ (ψ ∘ θ) p :=
    (hψ (θ p) hp).comp p (cylinderChart_symm_smooth q p)
  have hreg : ContDiffAt ℝ ∞ (fun y => scale * g.parametrizedCoefficients (ψ ∘ θ) y
      (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)) p :=
    contDiffAt_const.mul (((g.contDiffAt_parametrizedCoefficients hmap).clm_apply
      (contDiffAt_const (c := roundCylinderCoordinateBasis a))).clm_apply
        (contDiffAt_const (c := roundCylinderCoordinateBasis b)))
  apply hreg.congr_of_eventuallyEq
  have hnear := (hPhi.continuous.comp
    (cylinderChart_symm_smooth q).continuous).continuousAt.tendsto.eventually
    (hU.mem_nhds hp)
  filter_upwards [hnear] with y hy
  have heq := roundCylinderTensorCoefficient_pullback_eq g q ψ y
    ((hψ (θ y) hy).mdifferentiableAt (by simp)) a b
  have hforward := ((e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt
    (by simp)
  have hchain := mfderiv_comp (θ y) hforward ((hPhi (θ y)).mdifferentiableAt (by simp))
  have hcoef : roundCylinderTensorCoefficient (generalizedCylinderPullback e Phi s)
      (chartAt E₂ q) y a b =
      scale * roundCylinderTensorCoefficient (roundCylinderPullback g ψ) (chartAt E₂ q) y a b := by
    simp only [roundCylinderTensorCoefficient, generalizedCylinderPullback, dif_pos hs,
      roundCylinderPullback, GeneralizedFlowCylinder.pullbackInner]
    rw [hchain]
    rfl
  rw [hcoef, heq]
  rfl

private theorem locally_uniform_cylinder_errorJets
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (Phi : RoundCylinderSpace → G.limit.sliceCarrier.carrier)
    (hPhi : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Phi)
    (z₀ : RoundCylinderSpace) (R : ℝ) (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ∃ V : Set RoundCylinderSpace, V ∈ 𝓝 z₀ ∧
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ V, z.2 ∈ Icc (-R) R →
        ∀ s ∈ Icc (-1 : ℝ) 0, ∀ r ≤ m, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ r (fun y =>
            roundCylinderTensorCoefficient (generalizedCylinderPullback (G.embedding k) Phi s)
              (chartAt E₂ z.1) y a b -
            roundCylinderTensorCoefficient (roundCylinderPullback (G.limit.flow.metric s) Phi)
              (chartAt E₂ z.1) y a b) (0, z.2)‖ < rho := by
  classical
  let : NormedAddCommGroup (E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let a : G.limit.sliceCarrier.carrier := Phi z₀
  let c := extChartAt (𝓡 3) a
  obtain ⟨H, hH, haH, hHt⟩ := exists_compact_subset
    (isOpen_extChartAt_target (I := 𝓡 3) a) (mem_extChartAt_target (I := 𝓡 3) a)
  obtain ⟨D, hD, hDnear⟩ := cylinder_exists_local_parametrization_jet_bound Phi hPhi
    a z₀.1 z₀.2 R (m + 1) (mem_extChartAt_source a)
  choose C hC hbound using fun r : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound
      (E := RoundCylinderCoordinates) (F := E₃) (G := ℝ) r hD
  let C₀ : ℝ := ∑ r : Fin (m + 1), C r
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun r _ => hC r)
  let eta := rho / (C₀ + 1)
  have heta : 0 < eta := div_pos hrho (by linarith)
  have hsmall : C₀ * eta < rho := by
    have hscale : (C₀ + 1) * eta = rho := by
      dsimp [eta]
      field_simp
    nlinarith
  have hchart : ∀ᶠ z in 𝓝 z₀, Phi z ∈ c.source :=
    hPhi.continuous.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a))
  have hHnear : ∀ᶠ z in 𝓝 z₀, c (Phi z) ∈ H :=
    ((continuousAt_extChartAt a).comp hPhi.continuous.continuousAt).tendsto.eventually
      (mem_interior_iff_mem_nhds.mp haH)
  let V : Set RoundCylinderSpace := {z | Phi z ∈ c.source ∧ c (Phi z) ∈ H ∧
    (z.2 ∈ Icc (-R) R → ∀ r ≤ m + 1,
      ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
        c (Phi ((chartAt E₂ z.1).symm y.1, y.2))) (0, z.2)‖ ≤ D)}
  have hV : V ∈ 𝓝 z₀ := by
    filter_upwards [hchart, hHnear, hDnear] with z hz₁ hz₂ hz₃
    exact ⟨hz₁, hz₂, hz₃⟩
  have hcompact : IsCompact (c.symm '' H) :=
    hH.image_of_continuousOn ((continuousOn_extChartAt_symm a).mono hHt)
  obtain ⟨j₀, hj₀⟩ := blowup_exists_exhaustion_superset G hcompact
  have hdom : Icc (-1 : ℝ) 0 ×ˢ H ⊆ {z | z ∈ blowupMetricChartDomain G.limit a ∧
      c.symm z.2 ∈ G.exhaustion.space j₀} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    exact ⟨⟨hJI hs, hHt hy⟩, hj₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨k₀, _, hk₀⟩ := blowup_uniform_bilinear_errorJets G a j₀ m
    (Icc (-1 : ℝ) 0 ×ˢ H) (isCompact_Icc.prod hH) hdom eta heta
  refine ⟨V, hV, ?_⟩
  filter_upwards [eventually_ge_atTop k₀] with k hk z hz hzR s hs r hr i l
  rcases hz with ⟨hzchart, hzH, hzjets⟩
  let φ : RoundCylinderCoordinates → G.limit.sliceCarrier.carrier := fun y =>
    Phi ((chartAt E₂ z.1).symm y.1, y.2)
  let f : RoundCylinderCoordinates → E₃ := c ∘ φ
  let x : RoundCylinderCoordinates := (0, z.2)
  let T : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    ∑ v : Fin 3, ∑ w : Fin 3,
      (blowupPullbackCoefficient (G.embedding k) a v w (s, y) -
        FlowCarrier.coordinateCoefficient G.limit.carrier a
          (fun t x v w => (G.limit.flow.metric t).inner x v w) v w (s, y)) •
        (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ v)).smulRight
          (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ w))
  have hφx : φ x = Phi z := by simp only [φ, x, sphere_chart_symm_zero]
  have hfx : f x = c (Phi z) := congrArg c hφx
  have hzK : (s, c (Phi z)) ∈ Icc (-1 : ℝ) 0 ×ˢ H := ⟨hs, hzH⟩
  have hsource := (hk₀ k hk).1 hzK
  have hφ : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ φ x :=
    (hPhi _).comp x (cylinderChart_symm_smooth z.1 x)
  have hchartx : φ x ∈ c.source := by rw [hφx]; exact hzchart
  have hf : ContDiffAt ℝ ∞ f x := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_extChartAt (I := 𝓡 3) (x := a) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source a).mem_nhds hchartx)).comp x hφ)
  have hT : ContDiffAt ℝ ∞ T (f x) := by
    rw [hfx]
    exact ((hk₀ k hk).2 _ hzK).1
  have hTjet (j : ℕ) (hj : j ≤ r) : ‖iteratedFDeriv ℝ j T (f x)‖ ≤ eta := by
    rw [hfx]
    exact (((hk₀ k hk).2 _ hzK).2 j (hj.trans hr)).le
  let r' : Fin (m + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  have hpullback := hbound r' f T x hf hT
    (fun j hj => hzjets hzR j (hj.trans (Nat.add_le_add_right hr 1))) eta heta.le hTjet
  let P := fun y => (T (f y)).bilinearComp (fderiv ℝ f y) (fderiv ℝ f y)
  have hP : ContDiffAt ℝ ∞ P x := bilinearPullback_contDiffAt hf hT
  have heq : (fun y => roundCylinderTensorCoefficient
      (generalizedCylinderPullback (G.embedding k) Phi s) (chartAt E₂ z.1) y i l -
      roundCylinderTensorCoefficient (roundCylinderPullback (G.limit.flow.metric s) Phi)
        (chartAt E₂ z.1) y i l) =ᶠ[𝓝 x] (cylinderErrorEvaluation i l) ∘ P := by
    have hnear := hφ.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source a).mem_nhds hchartx)
    filter_upwards [hnear] with y hy
    exact cylinder_coefficient_error_fixed_chart (G.embedding k) Phi z.1 a hsource.1 y
      ((hPhi _).mdifferentiableAt (by simp)) hy i l
  rw [(heq.iteratedFDeriv ℝ r).self_of_nhds]
  have hpost := (cylinderErrorEvaluation i l).norm_iteratedFDeriv_comp_left
    hP (by exact_mod_cast le_top : (r : ℕ∞ω) ≤ ∞)
  calc
    _ ≤ ‖iteratedFDeriv ℝ r P x‖ := hpost.trans
      ((mul_le_mul_of_nonneg_right (norm_cylinderErrorEvaluation_le i l)
        (norm_nonneg _)).trans_eq (one_mul _))
    _ ≤ C r' * eta := hpullback
    _ ≤ C₀ * eta := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ r')) heta.le
    _ < rho := hsmall

theorem blowup_uniform_cylinder_coefficientJets
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (Phi : RoundCylinderSpace → G.limit.sliceCarrier.carrier)
    (hPhi : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Phi)
    (R : ℝ) (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ∀ᶠ k : ℕ in atTop,
      Icc (-1 : ℝ) 0 ⊆ Icc (-G.exhaustion.time k) 0 ∧
      Phi '' (univ ×ˢ Icc (-R) R) ⊆ G.exhaustion.space k ∧
      (∀ s ∈ Icc (-1 : ℝ) 0, ∀ q : UnitTwoSphere, ∀ p : RoundCylinderCoordinates,
        p.2 ∈ Icc (-R) R → ∀ a b : Fin 3,
          ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
            (generalizedCylinderPullback (G.embedding k) Phi s) (chartAt E₂ q) y a b) p) ∧
      ∀ z : RoundCylinderSpace, z.2 ∈ Icc (-R) R →
        ∀ s ∈ Icc (-1 : ℝ) 0, ∀ r ≤ m, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
            roundCylinderTensorCoefficient (generalizedCylinderPullback (G.embedding k) Phi s)
              (chartAt E₂ z.1) y a b -
            roundCylinderTensorCoefficient (roundCylinderPullback (G.limit.flow.metric s) Phi)
              (chartAt E₂ z.1) y a b) (0, z.2)‖ < rho := by
  classical
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  obtain ⟨j₀, hj₀⟩ := blowup_exists_exhaustion_superset G (hK.image hPhi.continuous)
  choose V hV hbound using fun z : RoundCylinderSpace =>
    locally_uniform_cylinder_errorJets G hJI Phi hPhi z R m rho hrho
  obtain ⟨cover, _, hcover⟩ := hK.elim_nhds_subcover V (fun z _ => hV z)
  filter_upwards [G.exhaustion.time_cofinal (Icc (-1 : ℝ) 0) isCompact_Icc hJI,
    eventually_ge_atTop j₀, cover.eventually_all.mpr (fun z _ => hbound z)] with k htime hk hboundk
  have hspace : Phi '' K ⊆ G.exhaustion.space k :=
    fun y hy => G.exhaustion.space_increasing hk (hj₀ hy)
  refine ⟨htime, hspace, ?_, ?_⟩
  · intro s hs q p hp a b
    exact captured_cylinderCoefficient_contDiffAt (G.embedding k) (G.exhaustion.space_open k)
      Phi hPhi (htime hs) q p (hspace ⟨_, ⟨mem_univ _, hp⟩, rfl⟩) a b
  · intro z hz
    have hzK : z ∈ K := ⟨mem_univ _, hz⟩
    obtain ⟨q, hq, hzq⟩ : ∃ q ∈ cover, z ∈ V q := by
      simpa only [mem_iUnion, exists_prop] using hcover hzK
    exact hboundk q hq z hzq hz

end PoincareConjecture.M32
