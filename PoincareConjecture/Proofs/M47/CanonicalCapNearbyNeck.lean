import PoincareConjecture.Proofs.M47.CanonicalCapNearbyErrors
import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckImage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 SpacetimeBounds Proofs.M46

local notation "E" => StandardCapSpace
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

noncomputable local instance capNearbyNeckCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capNearbyNeckCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace



theorem exists_actualCap_nearby_neck_coefficient_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v nu : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hv : v ∈ Icc 0 theta)
    (N : EpsilonNeck (standard.flow.metric v))
    (hsource : N.carrier ⊆ g0.metric.ball 0 A)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) (hnu : 0 < nu) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
      s ≤ theta → |s - v| < delta →
      let phi := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      let g' := m01RescaledMetric (F.metric (t + s / Q)) Q
        (sq_pos_of_pos (inv_pos.mpr hh))
      ∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun w u u' => N.scale⁻¹ ^ 2 *
            roundCylinderPullback g' (phi ∘ N.coordinate_map) w u u')
              (chartAt E₂ q) y a b -
          roundCylinderTensorCoefficient (fun w u u' => N.scale⁻¹ ^ 2 *
            roundCylinderPullback (standard.flow.metric v) N.coordinate_map w u u')
              (chartAt E₂ q) y a b) (0, z)‖ ≤ nu := by
  have hNK : N.carrier ⊆ {x : E | g0.metric.edist 0 x ≤ ENNReal.ofReal A} := by
    intro x hx
    exact (show g0.metric.edist 0 x < ENNReal.ofReal A from hsource hx).le
  obtain ⟨C, hC, hnative⟩ := exists_cap_neck_bilinear_error_jet_bound N m hm
    (M36.standard_closed_ball_compact g0 hA.le) hNK
  let alpha := N.scale⁻¹ ^ 2
  have halpha : 0 < alpha := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let tau := nu / (C * alpha)
  have htau : 0 < tau := div_pos hnu (mul_pos hC halpha)
  obtain ⟨eta0, delta, heta0, hdelta, hambient⟩ :=
    exists_actualCap_nearby_coordinate_tolerance standard htheta hA m htau
  refine ⟨eta0, delta, heta0, hdelta, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetamax comparison hh s hs hst hnear
  have hambient' := hambient F hinitial S hS t hT hn i J U e initial eta heta hetamax
    comparison s hs hst v hv hnear
  cases hinitial
  cases hS
  let V := F.standard_initial.metric.ball 0 A
  have hV : IsOpen V := (capInitialPartialDiffeomorph initial).open_source
  have himage : initial.chart '' V = U := comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hmap : MapsTo initial.chart V U := fun _ hx => himage ▸ mem_image_of_mem initial.chart hx
  let phi := actualCapSliceChart e initial comparison s hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + s / Q)) Q (sq_pos_of_pos (inv_pos.mpr hh))
  let coeff := capComparisonCoefficients e initial.chart s hs
  let T : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun x => alpha • (coeff x - (standard.flow.metric v).euclideanCoefficients x)
  have hcoeff := capComparisonCoefficients_smooth e hU hV initial.chart_smooth hmap s hs
  have hT (x : E) (hx : x ∈ N.carrier) : ContDiffAt ℝ ∞ T x :=
    ((hcoeff.contDiffAt (hV.mem_nhds (hsource hx))).sub
      ((standard.flow.metric v).contDiffAt_euclideanCoefficients x)).const_smul alpha
  have hTjet (x : E) (hx : x ∈ N.carrier) (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j T x‖ ≤ alpha * tau := by
    have hnew := hcoeff.contDiffAt (hV.mem_nhds (hsource hx))
    have hold := (standard.flow.metric v).contDiffAt_euclideanCoefficients x
    change ‖iteratedFDeriv ℝ j
      (fun x => alpha • (coeff x - (standard.flow.metric v).euclideanCoefficients x)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hnew.sub hold).of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs,
      abs_of_pos halpha, fun_iteratedFDeriv_sub_apply
        (hnew.of_le (by exact_mod_cast le_top)) (hold.of_le (by exact_mod_cast le_top))]
    exact mul_le_mul_of_nonneg_left (hambient' x (hsource hx) j hj) halpha.le
  have hphismooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ phi V := by
    simpa only [phi, actualCapSliceChart_source] using
      (actualCapSliceChart e initial comparison s hs).contMDiffOn_toFun
  have hmetric (x : E) (hx : x ∈ V) (u u' : E) :
      g'.inner (phi x) (mfderiv (𝓡 3) (𝓡 3) phi x u)
        (mfderiv (𝓡 3) (𝓡 3) phi x u') = coeff x u u' :=
    actualCapSliceChart_metric e initial comparison s hs hh hx u u'
  dsimp only
  intro q z hz j hj a b
  let tensor : RoundCylinderTwoTensor := fun w u u' => T (N.coordinate_map w)
    (mfderiv Ic (𝓡 3) N.coordinate_map w u) (mfderiv Ic (𝓡 3) N.coordinate_map w u')
  have hbound := hnative T hT (alpha * tau) (mul_nonneg halpha.le htau.le)
    hTjet q z hz j hj a b
  have heq : (fun y =>
      roundCylinderTensorCoefficient (fun w u u' => N.scale⁻¹ ^ 2 *
        roundCylinderPullback g' (phi ∘ N.coordinate_map) w u u') (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient (fun w u u' => N.scale⁻¹ ^ 2 *
        roundCylinderPullback (standard.flow.metric v) N.coordinate_map w u u')
        (chartAt E₂ q) y a b) =ᶠ[𝓝 (0, z)]
      (fun y => roundCylinderTensorCoefficient tensor (chartAt E₂ q) y a b) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (0, z) ∈ (univ : Set E₂) ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hz⟩)] with y hy
    have h := cap_neck_image_coefficient_difference N g' hV hphismooth hsource coeff
      hmetric q hy.2 a b
    change alpha * roundCylinderTensorCoefficient (roundCylinderPullback g'
      (phi ∘ N.coordinate_map)) (chartAt E₂ q) y a b -
      alpha * roundCylinderTensorCoefficient (roundCylinderPullback (standard.flow.metric v)
        N.coordinate_map) (chartAt E₂ q) y a b = _
    rw [← mul_sub, h]
    rfl
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  apply hbound.trans_eq
  dsimp only [tau]
  field_simp [hC.ne', halpha.ne']



theorem exists_actualCap_nearby_neck_normalized_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hv : v ∈ Icc 0 theta)
    (N : EpsilonNeck (standard.flow.metric v))
    (hconnection : N.connection = standard.flow.connection v)
    (hsource : N.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
      s ≤ theta → |s - v| < delta →
      let phi := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      let R := (F.connection (t + s / Q)).scalarCurvature (phi N.center)
      0 < R ∧ RoundCylinderClose N.epsilon 0 (fun z u u' =>
        R * roundCylinderPullback (F.metric (t + s / Q)) (phi ∘ N.coordinate_map) z u u') := by
  let D : RoundCylinderTwoTensor := fun z u u' => N.scale⁻¹ ^ 2 *
    roundCylinderPullback (standard.flow.metric v) N.coordinate_map z u u'
  obtain ⟨rho, hrho, sigma, hsigma, hsigmaHalf, hnormalize⟩ :=
    exists_cap_neck_normalization_tolerance N.epsilon_pos D N.metric_comparison.close
  obtain ⟨etaE, deltaE, hetaE, hdeltaE, herror⟩ :=
    exists_actualCap_nearby_neck_coefficient_tolerance standard htheta hA hv N hsource
      (Nat.floor N.epsilon⁻¹) le_rfl hrho
  let nu := sigma / N.scale ^ 2
  have hnu : 0 < nu := div_pos hsigma (sq_pos_of_pos N.scale_pos)
  obtain ⟨etaA, deltaA, hetaA, hdeltaA, hanalytic⟩ :=
    exists_actualCap_nearby_analytic_tolerance standard htheta hA hnu
  refine ⟨min etaE etaA, min deltaE deltaA, lt_min hetaE hetaA,
    lt_min hdeltaE hdeltaA, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetasmall comparison hh s hs hst hnear
  have herror' := herror F hinitial S hS t hT hn i J U e initial eta heta
    (hetasmall.trans (min_le_left _ _)) comparison hh s hs hst
    (hnear.trans_le (min_le_left _ _))
  have hanalytic' := hanalytic F hinitial S hS t hT hn i J U e initial eta heta
    (hetasmall.trans (min_le_right _ _)) comparison hh s hs hst v hv
    (hnear.trans_le (min_le_right _ _))
  cases hinitial
  cases hS
  let phi := actualCapSliceChart e initial comparison s hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + s / Q)) Q (sq_pos_of_pos (inv_pos.mpr hh))
  let R := (F.connection (t + s / Q)).scalarCurvature (phi N.center)
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
    hnormalize B hB herror' beta hbeta
  dsimp only
  refine ⟨hR, hclose.congr_cylinder ?_⟩
  intro z _ u u'
  change (N.scale ^ 2 * ((F.parameters.h t) ^ 2 * R)) *
    (N.scale⁻¹ ^ 2 * ((F.parameters.h t)⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (t + s / Q)) (phi ∘ N.coordinate_map) z u u')) =
    R * roundCylinderPullback (F.metric (t + s / Q)) (phi ∘ N.coordinate_map) z u u'
  field_simp [N.scale_pos.ne', hh.ne']



theorem exists_actualCap_nearby_image_neck_tolerance {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta A v : ℝ}
    (htheta : theta < 1) (hA : 0 < A) (hv : v ∈ Icc 0 theta)
    (N : EpsilonNeck (standard.flow.metric v))
    (hconnection : N.connection = standard.flow.connection v)
    (hsource : N.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
      s ≤ theta → |s - v| < delta →
      let phi := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      ∃ Eimage : EpsilonNeck (F.metric (t + s / Q)),
        Eimage.epsilon = N.epsilon ∧ Eimage.center = phi N.center ∧
        Eimage.connection = F.connection (t + s / Q) ∧
        Eimage.carrier = phi '' N.carrier ∧ Eimage.central_sphere = phi '' N.central_sphere ∧
        Eimage.coordinate_map = phi ∘ N.coordinate_map ∧
        Eimage.coordinate_inverse = N.coordinate_inverse ∘ phi.symm ∧
        ∀ a b : ℝ, -N.epsilon⁻¹ ≤ a → b ≤ N.epsilon⁻¹ →
          Eimage.region a b = phi '' N.region a b := by
  obtain ⟨eta0, delta, heta0, hdelta, hcompare⟩ :=
    exists_actualCap_nearby_neck_normalized_tolerance standard htheta hA hv N hconnection hsource
  refine ⟨eta0, delta, heta0, hdelta, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetasmall comparison hh s hs hst hnear
  have h := hcompare F hinitial S hS t hT hn i J U e initial eta heta hetasmall
    comparison hh s hs hst hnear
  apply exists_cap_neck_image_of_normalized_comparison N
    (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
    (actualCapSliceChart e initial comparison s hs) _ h.1 h.2
  rw [actualCapSliceChart_source, hinitial]
  exact hsource

end PoincareConjecture.Proofs.M47
