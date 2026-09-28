import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckNormalization
import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckError
import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticComparison
import PoincareConjecture.Proofs.M34.Standard.CapIsometryPullback









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

local notation "E" => StandardCapSpace
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)




theorem exists_actualCap_neck_normalized_comparison_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hvtheta : v ≤ theta)
    (N : EpsilonNeck (standard.flow.metric v))
    (hconnection : N.connection = standard.flow.connection v)
    (hsource : N.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (hs : v ∈ J),
      let phi := actualCapSliceChart e initial comparison v hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      let R := (F.connection (t + v / Q)).scalarCurvature (phi N.center)
      0 < R ∧ RoundCylinderClose N.epsilon 0 (fun z u u' =>
        R * roundCylinderPullback (F.metric (t + v / Q)) (phi ∘ N.coordinate_map) z u u') := by
  let D : RoundCylinderTwoTensor := fun z u u' => N.scale⁻¹ ^ 2 *
    roundCylinderPullback (standard.flow.metric v) N.coordinate_map z u u'
  obtain ⟨rho, hrho, sigma, hsigma, hsigmaHalf, hnormalize⟩ :=
    exists_cap_neck_normalization_tolerance N.epsilon_pos D N.metric_comparison.close
  obtain ⟨C, hC, herror⟩ := exists_actualCap_neck_coefficient_error_bound standard htheta hA
    hvtheta N hsource (Nat.floor N.epsilon⁻¹) le_rfl
  let nu := sigma / N.scale ^ 2
  have hnu : 0 < nu := div_pos hsigma (sq_pos_of_pos N.scale_pos)
  obtain ⟨etaA, hetaA, hanalytic⟩ :=
    exists_actualCap_analytic_comparison_tolerance standard htheta hA hnu
  let m := Nat.floor N.epsilon⁻¹
  let eta0 := min etaA (min (rho / C) (1 / ((m : ℝ) + 1)))
  have heta0 : 0 < eta0 := lt_min hetaA
    (lt_min (div_pos hrho hC) (div_pos zero_lt_one (by positivity)))
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetasmall comparison hh hs
  have hetaAnalytic : eta ≤ etaA := hetasmall.trans (min_le_left _ _)
  have hetaError : C * eta ≤ rho := by
    have h := (le_div_iff₀ hC).mp
      (hetasmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hetaOrder : eta ≤ 1 / ((m : ℝ) + 1) :=
    hetasmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have herror' := herror F hinitial S hS t hT hn i J U e initial eta heta hetaOrder
    comparison hh hs
  have hanalytic' := hanalytic F hinitial S hS t hT hn i J U e initial eta heta
    hetaAnalytic comparison hh v hs hvtheta
  cases hinitial
  cases hS
  let phi := actualCapSliceChart e initial comparison v hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + v / Q)) Q (sq_pos_of_pos (inv_pos.mpr hh))
  let R := (F.connection (t + v / Q)).scalarCurvature (phi N.center)
  let beta := N.scale ^ 2 * ((F.parameters.h t) ^ 2 * R)
  have hcenter := N.central_sphere_subset N.center_on_central_sphere
  have hscalar : |(F.parameters.h t) ^ 2 * R - N.connection.scalarCurvature N.center| ≤ nu := by
    rw [hconnection]
    exact (norm_fst_le _).trans (hanalytic' N.center (hsource hcenter))
  have hnormal : N.scale ^ 2 * N.connection.scalarCurvature N.center = 1 := by
    rw [N.scale_eq_scalar, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg N.scalar_center_pos.le, ← Real.sqrt_eq_rpow, inv_pow,
      Real.sq_sqrt N.scalar_center_pos.le, inv_mul_cancel₀ N.scalar_center_pos.ne']
  have hbeta : |beta - 1| ≤ sigma := by
    have heq : beta - 1 = N.scale ^ 2 *
        ((F.parameters.h t) ^ 2 * R - N.connection.scalarCurvature N.center) := by
      dsimp only [beta]
      rw [mul_sub, hnormal]
    rw [heq, abs_mul, abs_of_pos (sq_pos_of_pos N.scale_pos)]
    apply (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _)).trans_eq
    dsimp only [nu]
    field_simp [N.scale_pos.ne']
  have hbetaPos : 0 < beta := by
    have h := (abs_le.mp (hbeta.trans hsigmaHalf)).1
    linarith
  have hR : 0 < R := by
    by_contra hnot
    have h := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sq_nonneg N.scale) (sq_nonneg (F.parameters.h t))) (le_of_not_gt hnot)
    dsimp only [beta] at hbetaPos
    nlinarith
  let B : RoundCylinderTwoTensor := fun z u u' => N.scale⁻¹ ^ 2 *
    roundCylinderPullback g' (phi ∘ N.coordinate_map) z u u'
  have hsource' : N.carrier ⊆ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource
  have hsmooth : ContMDiffOn Ic (𝓡 3) ∞ (phi ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    phi.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource' (N.coordinate_map_mem_of_axial_mem hz.2))
  have hB : RoundCylinderTensorSmoothOn N.epsilon B :=
    (M34.capPersistence_roundCylinderTensorSmoothOn_pullback g' hsmooth).const_mul
  have hclose : RoundCylinderClose N.epsilon 0 (fun z u u' => beta * B z u u') :=
    hnormalize B hB (fun q z hz j hj a b => (herror' q z hz j hj a b).trans hetaError)
      beta hbeta
  dsimp only
  refine ⟨hR, hclose.congr_cylinder ?_⟩
  intro z _ u u'
  change (N.scale ^ 2 * ((F.parameters.h t) ^ 2 * R)) *
    (N.scale⁻¹ ^ 2 * ((F.parameters.h t)⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (t + v / Q)) (phi ∘ N.coordinate_map) z u u')) =
    R * roundCylinderPullback (F.metric (t + v / Q)) (phi ∘ N.coordinate_map) z u u'
  field_simp [N.scale_pos.ne', hh.ne']

end PoincareConjecture.M47
