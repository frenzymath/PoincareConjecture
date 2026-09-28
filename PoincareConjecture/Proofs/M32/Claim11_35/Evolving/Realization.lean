import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.Jets
import PoincareConjecture.Proofs.M32.Claim11_35.ScalarScaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}

private noncomputable def evolvingRealizationRechart
    {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) : E3 ≃L[ℝ] V :=
  (RiemannianMetric.lineModelEquiv 2).symm.trans
    (evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one))

private noncomputable def evolvingRealizationMap
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) : E3 → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier :=
  fun y => N.time_cylinder.forward tau htau
    (N.coordinate_map ((chartAt E2 q).symm ((0, z) + evolvingRealizationRechart htau y).1,
      ((0, z) + evolvingRealizationRechart htau y).2))

private theorem evolvingRealizationMap_contMDiffAt
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) {x : E3}
    (hx : ((0, z) + evolvingRealizationRechart htau x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (evolvingRealizationMap N htau q z) x := by
  let p : V := (0, z) + evolvingRealizationRechart htau x
  let w : RoundCylinderSpace := ((chartAt E2 q).symm p.1, p.2)
  have hmem : N.coordinate_map w ∈ N.carrier := by
    let a : NeckDomain epsilon := (w.1, ⟨w.2, hx⟩)
    simpa only [N.coordinate_map_eq a, a] using (N.coordinate a).property
  have hc := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ w.1, hx⟩)
  have hf := (N.time_cylinder.forward_smooth tau htau).contMDiffAt
    (N.carrier_open.mem_nhds hmem)
  have ha : ContMDiffAt (𝓡 3) 𝓘(ℝ, V) ∞
      (fun y => (0, z) + evolvingRealizationRechart htau y) x :=
    (contDiffAt_const.add (evolvingRealizationRechart htau).contDiff.contDiffAt).contMDiffAt
  have hchart : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun y => ((chartAt E2 q).symm ((0, z) + evolvingRealizationRechart htau y).1,
        ((0, z) + evolvingRealizationRechart htau y).2)) x :=
    (cylinderChart_symm_smooth q p).comp x ha
  have hcoord : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y => N.coordinate_map
        ((chartAt E2 q).symm ((0, z) + evolvingRealizationRechart htau y).1,
          ((0, z) + evolvingRealizationRechart htau y).2)) x := hc.comp x hchart
  exact hf.comp x hcoord

set_option maxHeartbeats 800000 in

private theorem evolvingRealizationCoefficients_contDiffAt
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) {x : E3}
    (hx : ((0, z) + evolvingRealizationRechart htau x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContDiffAt ℝ ∞ (strongNeckEvolvingCoefficients N htau q z) x := by
  have hcoeff := (F.metric (t + tau / (N.scale⁻¹ ^ 2))).contDiffAt_parametrizedCoefficients
    (evolvingRealizationMap_contMDiffAt N htau q z hx)
  unfold strongNeckEvolvingCoefficients
  exact hcoeff.const_smul (N.scale⁻¹ ^ 2 / (1 - tau))

private theorem evolvingRealizationCoefficients_symm
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) (x v w : E3) :
    strongNeckEvolvingCoefficients N htau q z x v w =
      strongNeckEvolvingCoefficients N htau q z x w v := by
  change (N.scale⁻¹ ^ 2 / (1 - tau)) * (F.metric _).inner _ _ _ =
    (N.scale⁻¹ ^ 2 / (1 - tau)) * (F.metric _).inner _ _ _
  rw [(F.metric _).symm]

theorem exists_strongNeck_evolving_fourJet_realization {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilon₀ →
          ∀ {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) (q : UnitTwoSphere) {z : ℝ},
            z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
              ∃ (h : RiemannianMetric 3 E3) (_Dh : LeviCivitaData h),
                (h.euclideanCoefficients =ᶠ[𝓝 0] strongNeckEvolvingCoefficients N htau q z) ∧
                ∀ r : ℕ, r ≤ 4 →
                  ‖iteratedFDeriv ℝ r h.euclideanCoefficients 0 -
                    iteratedFDeriv ℝ r roundCylinderEuclideanMetric.euclideanCoefficients 0‖ <
                      delta := by
  obtain ⟨C, hC, hbound⟩ := exists_strongNeck_evolving_fourJet_bound.{u}
  let eta := min delta (1 / 2 : ℝ)
  have heta : 0 < eta := lt_min hdelta (by norm_num)
  refine ⟨min (1 / 200) (eta / (2 * C)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro F t epsilon N hsmall tau htau q z hz
  have hquarter : epsilon ≤ 1 / 4 :=
    (hsmall.trans (min_le_left _ _)).trans (by norm_num)
  have herror : C * epsilon < eta := by
    have h := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (hsmall.trans (min_le_right _ _))
    nlinarith
  let B := strongNeckEvolvingCoefficients N htau q z
  let L := evolvingRealizationRechart htau
  let U : Set E3 := {x | ((0, z) + L x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add L.continuous))
  have h0U : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hz
  have hB : ContDiffOn ℝ ∞ B U := fun x hx =>
    (evolvingRealizationCoefficients_contDiffAt N htau q z hx).contDiffWithinAt
  have hzerobound : ‖B 0 - roundCylinderEuclideanCoefficients 0‖ ≤ C * epsilon := by
    simpa only [norm_iteratedFDeriv_zero] using hbound N hquarter htau q hz 0 (by omega)
  have hzero : ‖B 0 - roundCylinderEuclideanCoefficients 0‖ < (1 / 2 : ℝ) :=
    hzerobound.trans_lt (herror.trans_le (min_le_right _ _))
  have hlow (v : E3) : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B 0 v v := by
    have he := ((B 0 - roundCylinderEuclideanCoefficients 0) v).le_opNorm v
    have he' := (B 0 - roundCylinderEuclideanCoefficients 0).le_opNorm v
    have habs : |B 0 v v - roundCylinderEuclideanCoefficients 0 v v| ≤
        ‖B 0 - roundCylinderEuclideanCoefficients 0‖ * ‖v‖ ^ 2 := by
      simpa only [sub_apply, Real.norm_eq_abs, mul_assoc, ← sq] using
        he.trans (mul_le_mul_of_nonneg_right he' (norm_nonneg v))
    have hmodel := roundCylinderEuclideanMetric_norm_sq_le v
    change ‖v‖ ^ 2 ≤ roundCylinderEuclideanCoefficients 0 v v at hmodel
    have hsmall := mul_le_mul_of_nonneg_right hzero.le (sq_nonneg ‖v‖)
    nlinarith [(abs_le.mp habs).1]
  have hclose : ∀ᶠ x in 𝓝 (0 : E3), ‖B x - B 0‖ < (1 / 4 : ℝ) := by
    have hc := ((hB.contDiffAt (hU.mem_nhds h0U)).continuousAt.sub
      (continuousAt_const (y := B 0))).norm
    exact hc.eventually (Iio_mem_nhds (by simp only [Pi.sub_apply, sub_self, norm_zero]; norm_num))
  obtain ⟨W, hW, hWo, h0W⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0U) hclose)
  have hWU : W ⊆ U := fun x hx => (hW hx).1
  have hpos : ∀ x ∈ W, ∀ v : E3, v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    have he := ((B x - B 0) v).le_opNorm v
    have he' := (B x - B 0).le_opNorm v
    have habs : |B x v v - B 0 v v| ≤ ‖B x - B 0‖ * ‖v‖ ^ 2 := by
      simpa only [sub_apply, Real.norm_eq_abs, mul_assoc, ← sq] using
        he.trans (mul_le_mul_of_nonneg_right he' (norm_nonneg v))
    have hsq := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hsmall := mul_lt_mul_of_pos_right (hW hx).2 hsq
    nlinarith [hlow v, (abs_le.mp habs).1]
  obtain ⟨h, Dh, U', hVo, h0V, _, heqV⟩ := RiemannianMetric.exists_local_realization
    hWo h0W B (hB.mono hWU) (fun x _ => evolvingRealizationCoefficients_symm N htau q z x) hpos
  have heq : h.euclideanCoefficients =ᶠ[𝓝 0] B :=
    Filter.Eventually.mono (hVo.mem_nhds h0V) heqV
  refine ⟨h, Dh, heq, ?_⟩
  intro r hr
  have hmodel : roundCylinderEuclideanMetric.euclideanCoefficients =
      roundCylinderEuclideanCoefficients := by funext x; ext v w; rfl
  have herr : (fun x => h.euclideanCoefficients x -
      roundCylinderEuclideanMetric.euclideanCoefficients x) =ᶠ[𝓝 0]
      (fun x => B x - roundCylinderEuclideanCoefficients x) := by
    filter_upwards [heq] with x hx
    rw [hx, hmodel]
  rw [← iteratedFDeriv_sub_apply
    ((h.contDiffAt_euclideanCoefficients 0).of_le (by exact_mod_cast le_top))
    ((roundCylinderEuclideanMetric.contDiffAt_euclideanCoefficients 0).of_le
      (by exact_mod_cast le_top))]
  simp only [Pi.sub_def]
  rw [(herr.iteratedFDeriv ℝ r).self_of_nhds]
  exact (hbound N hquarter htau q hz r hr).trans_lt (herror.trans_le (min_le_left _ _))

theorem strongNeck_evolving_realization_curvatures
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) {z : ℝ} (hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    {h : RiemannianMetric 3 E3} (Dh : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] strongNeckEvolvingCoefficients N htau q z) :
    let Q := N.scale⁻¹ ^ 2
    let p := N.time_cylinder.pointMap tau htau (N.coordinate_map (q, z))
    Dh.scalarCurvature 0 = (1 - tau) * F.scalar p / Q ∧
      Dh.laplacian Dh.scalarCurvature 0 =
        (1 - tau) ^ 2 *
          (F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 / Q ^ 2 := by
  let Q := N.scale⁻¹ ^ 2
  let a := 1 - tau
  let f := evolvingRealizationMap N htau q z
  let L := evolvingRealizationRechart htau
  let U : Set E3 := {x | ((0, z) + L x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add L.continuous))
  have h0U : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hz
  obtain ⟨W, hW, hWo, h0W⟩ := mem_nhds_iff.mp (heq.and (hU.mem_nhds h0U))
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f W := fun x hx =>
    (evolvingRealizationMap_contMDiffAt N htau q z (hW hx).2).contMDiffWithinAt
  have hmetric : ∀ x ∈ W, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner x v w = (Q / a) * (F.metric (t + tau / Q)).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    intro x hx v w
    change h.euclideanCoefficients x v w = _
    rw [(hW hx).1]
    rfl
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have ha : 0 < a := by dsimp only [a]; linarith [htau.2]
  have hzero : f 0 = N.time_cylinder.forward tau htau (N.coordinate_map (q, z)) := by
    simp only [f, evolvingRealizationMap, map_zero, add_zero,
      Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero]
  have hscalar := scalarCurvature_eq_of_local_homothety Dh (F.connection (t + tau / Q))
    (div_pos hQ ha) hWo hf hmetric h0W
  have hlap := scalarLaplacian_eq_of_local_homothety Dh (F.connection (t + tau / Q))
    (div_pos hQ ha) hWo hf hmetric h0W
  rw [hzero] at hscalar hlap
  constructor
  · change Dh.scalarCurvature 0 = a * (F.connection (t + tau / Q)).scalarCurvature
      (N.time_cylinder.forward tau htau (N.coordinate_map (q, z))) / Q
    rw [hscalar]
    field_simp
  · change Dh.laplacian Dh.scalarCurvature 0 = a ^ 2 *
      (F.connection (t + tau / Q)).laplacian (F.connection (t + tau / Q)).scalarCurvature
        (N.time_cylinder.forward tau htau (N.coordinate_map (q, z))) / Q ^ 2
    rw [hlap]
    field_simp

end PoincareConjecture.M32
