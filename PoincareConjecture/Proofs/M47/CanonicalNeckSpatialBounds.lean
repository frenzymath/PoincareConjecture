import PoincareConjecture.Proofs.M47.CanonicalNeckSpatialReadout
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCoordinateJets
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus
open Poincare.Geometry.Riemannian.SpaceForm

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

private noncomputable def spatialNeckCoefficientEvaluation (i l : Fin 3) :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis l)).comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (roundCylinderCoordinateBasis i))

private theorem spatialNeckCoefficientEvaluation_norm_le (i l : Fin 3) :
    ‖spatialNeckCoefficientEvaluation i l‖ ≤ 1 := by
  have hb (j : Fin 3) : ‖roundCylinderCoordinateBasis j‖ = 1 := by
    fin_cases j <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa only [spatialNeckCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, hb, mul_one, one_mul] using
      B.le_opNorm₂ (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis l)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M]



theorem exists_local_neck_metric_jet_bound
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    (z0 : RoundCylinderSpace) (hz0 : z0.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (R : ℝ) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ W : Set RoundCylinderSpace, W ∈ 𝓝 z0 ∧
      ∀ z ∈ W, z.2 ∈ Icc (-R) R → ∀ t ∈ Icc a b, ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
            (chartAt E₂ z.1) y i l) (0, z.2)‖ ≤ B := by
  classical
  let p := N.coordinate_map z0
  let c := extChartAt (𝓡 3) p
  obtain ⟨H, hH, hpH, hHt⟩ := exists_compact_subset
    (isOpen_extChartAt_target (I := 𝓡 3) p) (mem_extChartAt_target (I := 𝓡 3) p)
  obtain ⟨D, hD, hDnear⟩ := N.exists_local_parametrization_jet_bound
    p z0.1 z0.2 R (m + 1) hz0 (mem_extChartAt_source p)
  obtain ⟨A, hA, hAjet⟩ := metric_jets_bounded_on_compact_time_space hab F
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hH hHt m
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound (E := V) (F := E₃) (G := ℝ) j hD
  let B0 := ∑ j : Fin (m + 1), B j
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun j _ => hB j
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hmap : ContinuousAt N.coordinate_map z0 :=
    (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz0⟩)).continuousAt
  have hchart : ∀ᶠ z in 𝓝 z0, N.coordinate_map z ∈ c.source :=
    hmap.tendsto.eventually ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p))
  have hHnear : ∀ᶠ z in 𝓝 z0, c (N.coordinate_map z) ∈ H :=
    ((continuousAt_extChartAt p).comp hmap).tendsto.eventually
      (mem_interior_iff_mem_nhds.mp hpH)
  have haxis : ∀ᶠ z : RoundCylinderSpace in 𝓝 z0,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hz0)
  let W : Set RoundCylinderSpace := {z | N.coordinate_map z ∈ c.source ∧
    c (N.coordinate_map z) ∈ H ∧ z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
    (z.2 ∈ Icc (-R) R → ∀ j ≤ m + 1,
      ‖iteratedFDeriv ℝ j (fun y : V =>
        c (N.coordinate_map ((chartAt E₂ z.1).symm y.1, y.2))) (0, z.2)‖ ≤ D)}
  have hW : W ∈ 𝓝 z0 := by
    filter_upwards [hchart, hHnear, haxis, hDnear] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨max 1 (B0 * A), le_max_left _ _, W, hW, ?_⟩
  intro z hz hzR t ht j hj i l
  rcases hz with ⟨hzchart, hzH, hzaxis, hzjets⟩
  let phi : V → M := fun y => N.coordinate_map ((chartAt E₂ z.1).symm y.1, y.2)
  let f : V → E₃ := c ∘ phi
  let x : V := (0, z.2)
  let T := (F.metric t).pullbackCoefficients c.symm
  have hphix : phi x = N.coordinate_map z := by simp only [phi, x, sphere_chart_symm_zero]
  have hfx : f x = c (N.coordinate_map z) := congrArg c hphix
  have hN : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map
      ((chartAt E₂ z.1).symm x.1, x.2) := by
    simpa only [x, sphere_chart_symm_zero] using N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzaxis⟩)
  have hphi : ContMDiffAt 𝓘(ℝ, V) (𝓡 3) ∞ phi x :=
    hN.comp x (cylinderChart_symm_smooth z.1 x)
  have hchartx : phi x ∈ c.source := by rw [hphix]; exact hzchart
  have hf : ContDiffAt ℝ ∞ f x := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_extChartAt (I := 𝓡 3) (x := p) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source p).mem_nhds hchartx)).comp x hphi)
  have hT : ContDiffAt ℝ ∞ T (f x) :=
    ((F.metric t).contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (by rw [hfx]; exact hHt hzH))
  have hTjet (r : ℕ) (hr : r ≤ j) : ‖iteratedFDeriv ℝ r T (f x)‖ ≤ A := by
    rw [hfx]
    exact hAjet t ht _ hzH r (hr.trans hj)
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let P := fun y => (T (f y)).bilinearComp (fderiv ℝ f y) (fderiv ℝ f y)
  have hP : ContDiffAt ℝ ∞ P x := hf.bilinearPullback hT
  have hPjet : ‖iteratedFDeriv ℝ j P x‖ ≤ B j' * A :=
    hbound j' f T x hf hT
      (fun r hr => hzjets hzR r (hr.trans (Nat.add_le_add_right hj 1))) A hA0 hTjet
  have heq : (fun y => roundCylinderTensorCoefficient
      (roundCylinderPullback (F.metric t) N.coordinate_map) (chartAt E₂ z.1) y i l)
      =ᶠ[𝓝 x] (spatialNeckCoefficientEvaluation i l) ∘ P := by
    have hnear := hphi.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source p).mem_nhds hchartx)
    have hnearaxis : ∀ᶠ y : V in 𝓝 x, y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds hzaxis)
    filter_upwards [hnear, hnearaxis] with y hy hyaxis
    exact neck_metric_coefficient_fixed_native_chart (F.metric t) N.coordinate_map z.1 p y
      ((N.coordinate_map_smooth.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hyaxis⟩)).mdifferentiableAt
          (by simp)) hy i l
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ ‖spatialNeckCoefficientEvaluation i l‖ * ‖iteratedFDeriv ℝ j P x‖ :=
      (spatialNeckCoefficientEvaluation i l).norm_iteratedFDeriv_comp_left hP
        (by exact_mod_cast le_top)
    _ ≤ 1 * ‖iteratedFDeriv ℝ j P x‖ := mul_le_mul_of_nonneg_right
      (spatialNeckCoefficientEvaluation_norm_le i l) (norm_nonneg _)
    _ ≤ B j' * A := by simpa only [one_mul] using hPjet
    _ ≤ B0 * A := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun r _ => hB r) (Finset.mem_univ j')) hA0
    _ ≤ max 1 (B0 * A) := le_max_right _ _



theorem neck_metric_jets_bounded_on_closed_cylinder
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {R : ℝ} (hR : R < N.epsilon⁻¹) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t ∈ Icc a b, ∀ q : UnitTwoSphere,
      ∀ z ∈ Icc (-R) R, ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
            (chartAt E₂ q) y i l) (0, z)‖ ≤ B := by
  classical
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  let P (B : ℝ) (z : RoundCylinderSpace) : Prop :=
    ∀ t ∈ Icc a b, ∀ j ≤ m, ∀ i l : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
          (chartAt E₂ z.1) y i l) (0, z.2)‖ ≤ B
  have hlocal (q : RoundCylinderSpace) : ∃ B : ℝ, 1 ≤ B ∧
      ∃ W : Set RoundCylinderSpace, W ∈ 𝓝 q ∧ ∀ z ∈ K, z ∈ W → P B z := by
    by_cases hq : q ∈ K
    · have haxis : q.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
        ⟨(neg_lt_neg hR).trans_le hq.2.1, hq.2.2.trans_lt hR⟩
      obtain ⟨B, hB, W, hW, hbound⟩ :=
        exists_local_neck_metric_jet_bound hab F N q haxis R m
      exact ⟨B, hB, W, hW, fun z hz hzW => hbound z hzW hz.2⟩
    · exact ⟨1, le_rfl, Kᶜ, hK.isClosed.isOpen_compl.mem_nhds hq,
        fun _ hz hzW => False.elim (hzW hz)⟩
  choose B hB W hW hbound using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover W (fun q _ => hW q)
  have hB0 (q : RoundCylinderSpace) : 0 ≤ B q := zero_le_one.trans (hB q)
  have hsum : 0 ≤ ∑ q ∈ S, B q := Finset.sum_nonneg fun q _ => hB0 q
  refine ⟨1 + ∑ q ∈ S, B q, by linarith, ?_⟩
  intro t ht q z hz j hj i l
  obtain ⟨p, hp, hzp⟩ : ∃ p ∈ S, (q, z) ∈ W p := by
    simpa only [mem_iUnion, exists_prop] using hcover (show (q, z) ∈ K from ⟨mem_univ _, hz⟩)
  calc
    _ ≤ B p := hbound p (q, z) ⟨mem_univ _, hz⟩ hzp t ht j hj i l
    _ ≤ ∑ x ∈ S, B x := Finset.single_le_sum (fun x _ => hB0 x) hp
    _ ≤ 1 + ∑ x ∈ S, B x := by linarith

end PoincareConjecture.Proofs.M47
