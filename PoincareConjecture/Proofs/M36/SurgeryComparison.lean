import PoincareConjecture.Proofs.M36.ComparisonConvergence
import PoincareConjecture.Proofs.M36.ComparisonCovariantJets
import PoincareConjecture.Proofs.M36.ComparisonDilationJets
import PoincareConjecture.Proofs.M36.ComparisonParameters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1200000 in

theorem exists_surgeryMetric_standard_close (g₀ : StandardInitialMetric)
    (C q : ℝ) (hC : 0 ≤ C) {r : ℝ} (hr : 0 < r)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
        (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (hsmall : N.epsilon < 1 / 200),
        N.epsilon ≤ delta →
      Nonempty (SurgeryCapClose g₀
        (surgeryBallCarrier g₀ (surgeryOuterRadius g₀ N.epsilon))
        (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
          (neck_contraction_coefficient_pos N hsmall) hr)
        (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N)) N.scale eta) := by
  let R := eta⁻¹
  let t := radialEuclideanRadius g₀ R
  let m := ⌊eta⁻¹⌋₊
  have hR : 0 < R := inv_pos.mpr heta
  have ht : 0 < t := (radialEuclideanRadius_pos_iff g₀ R).mpr hR
  let K : Set E₃ := Metric.closedBall 0 t
  let Kbig : Set E₃ := Metric.closedBall 0 (2 * t + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKbig : IsCompact Kbig := isCompact_closedBall _ _
  obtain ⟨B0, hB0, hcovariant⟩ :=
    exists_comparison_covariant_jet_bound g₀.metric g₀.connection hK m
  let rho := eta / (2 * (B0 + 1))
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hbound : B0 * rho ^ 2 < eta ^ 2 := by
    dsimp [rho]
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < (2 * (B0 + 1)) ^ 2)).mpr
    have hc : B0 < (2 * (B0 + 1)) ^ 2 := by nlinarith [sq_nonneg B0]
    nlinarith only [mul_lt_mul_of_pos_right hc (sq_pos_of_pos heta)]
  obtain ⟨a, ha1, ha2, hdilation⟩ := exists_standardComparison_dilation g₀ hK m
    (by linarith only [hrho] : 0 < rho / 2)
  have ha : 0 < a := zero_lt_one.trans ha1
  let tolerance := rho / (2 * (2 : ℝ) ^ (m + 2))
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  obtain ⟨deltaN, hdN, hnatural⟩ :=
    exists_surgeryMetric_chart_jets_small g₀ C q hr hKbig m htolerance
  obtain ⟨deltaI, hdI, himage⟩ := exists_standardComparison_image_threshold C
    (standardComparison_radial_margin g₀ ha1 hR)
  refine ⟨min deltaN deltaI, lt_min hdN hdI, ?_⟩
  intro M _ _ _ g N hcut hsmall hepsilon
  let L := surgeryOuterRadius g₀ N.epsilon
  let H := surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
    (neck_contraction_coefficient_pos N hsmall) hr
  let f := dilatedSurgeryBallChart g₀ L a
  let B := fun p => N.connection.scalarCurvature N.center • H.pullbackCoefficients f p
  let F := fun p => N.connection.scalarCurvature N.center •
    H.pullbackCoefficients (surgeryBallChart g₀ L) p - g₀.metric.euclideanCoefficients p
  obtain ⟨hbigFit, hnaturalJets⟩ := hnatural N hcut
    (hepsilon.trans (min_le_left _ _)) (neck_contraction_coefficient_pos N hsmall)
  have hroom := (himage N.epsilon N.epsilon_pos.le
    (hepsilon.trans (min_le_right _ _))).2
  have hvnorm : ‖(2 * t + 1) • EuclideanSpace.basisFun (Fin 3) ℝ 0‖ = 2 * t + 1 := by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,
      mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hLroom : 2 * t + 1 < radialEuclideanRadius g₀ L := by
    have hv := hbigFit (show (2 * t + 1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 ∈ Kbig by
      simpa only [Kbig, Metric.mem_closedBall, dist_zero_right, hvnorm] using
        (le_refl (2 * t + 1)))
    simpa only [Metric.mem_ball, dist_zero_right, hvnorm] using hv
  have hfit : a * radialEuclideanRadius g₀ R ≤ radialEuclideanRadius g₀ L := by
    change a * t ≤ _
    nlinarith only [ha2, ht, hLroom]
  let U : Set E₃ := Metric.ball 0 (t + 1 / 4)
  have hU : IsOpen U := Metric.isOpen_ball
  have hKU : K ⊆ U := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith only [hx]
  have hmapBig (x : E₃) (hx : x ∈ U) : a • x ∈ Kbig := by
    have hxn : ‖x‖ < t + 1 / 4 := by simpa only [U, Metric.mem_ball, dist_zero_right] using hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hm := mul_lt_mul_of_pos_left hxn ha
    nlinarith only [hm, ha2, ht]
  have hmapsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    (surgeryBallChart_contMDiffOn g₀ L).comp
      ((contDiff_id.const_smul a).contMDiff.contMDiffOn)
      (fun x hx => hbigFit (hmapBig x hx))
  have hBsmooth : ContDiffOn ℝ ∞ B U := by
    intro x hx
    exact ((H.contDiffAt_pullbackCoefficients
      ((hmapsmooth x hx).contMDiffAt (hU.mem_nhds hx))).const_smul
        (N.connection.scalarCurvature N.center)).contDiffWithinAt
  have hF (x : E₃) (hx : x ∈ Kbig) : ContDiffAt ℝ ∞ F x :=
    ((H.contDiffAt_pullbackCoefficients
      ((surgeryBallChart_contMDiffOn g₀ L x (hbigFit hx)).contMDiffAt
        (Metric.isOpen_ball.mem_nhds (hbigFit hx)))).const_smul
          (N.connection.scalarCurvature N.center)).sub
            (g₀.metric.contDiffAt_euclideanCoefficients x)
  have hD : ContDiff ℝ ∞ (standardDilationError g₀ a) :=
    (standardDilationError_joint_contDiff g₀).comp
      (f := fun x : E₃ => (a, x)) (contDiff_const.prodMk contDiff_id)
  have hsourceOpen : IsOpen (g₀.metric.ball 0 R) := by
    rw [standard_ball_eq_euclidean g₀ hR]
    exact Metric.isOpen_ball
  have hsourceK : g₀.metric.ball 0 R ⊆ K := by
    rw [standard_ball_eq_euclidean g₀ hR]
    exact Metric.ball_subset_closedBall
  have hjet (p : E₃) (hp : p ∈ g₀.metric.ball 0 R) (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (B - g₀.metric.euclideanCoefficients) p‖ ≤ rho := by
    have hpK := hsourceK hp
    have hpa := hmapBig p (hKU hpK)
    have heq : B - g₀.metric.euclideanCoefficients =ᶠ[nhds p]
        fun x => a ^ 2 • F (a • x) + standardDilationError g₀ a x := by
      filter_upwards [hsourceOpen.mem_nhds hp] with x hx
      exact dilatedSurgeryBallChart_error g₀ ha hR hfit H
        (N.connection.scalarCurvature N.center) hx
    have hscaled : ContDiffAt ℝ ∞ (fun x => a ^ 2 • F (a • x)) p :=
      ((hF _ hpa).comp p (contDiffAt_id.const_smul a)).const_smul (a ^ 2)
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds,
      fun_iteratedFDeriv_add_apply (i := j) (hscaled.of_le (by exact_mod_cast le_top))
        (hD.contDiffAt.of_le (by exact_mod_cast le_top))]
    apply (norm_add_le _ _).trans
    have hb := norm_iteratedFDeriv_dilation_at ha ha2.le (hF _ hpa)
      htolerance.le (hnaturalJets j hj _ hpa) hj
    have hc := hdilation j hj p hpK
    have htolerance_eq : (2 : ℝ) ^ (m + 2) * tolerance = rho / 2 := by
      dsimp [tolerance]
      field_simp
    rw [htolerance_eq] at hb
    linarith only [hb, hc]
  have hbeta : 0 < (1 - 6 * N.epsilon) * Real.exp (-2 * C * N.epsilon) :=
    mul_pos (neck_contraction_coefficient_pos N hsmall) (Real.exp_pos _)
  refine ⟨{
    eta_pos := heta
    scale_pos := N.scale_pos
    map := f
    inverse := dilatedSurgeryBallInverse g₀ L a
    map_tip := dilatedSurgeryBallChart_zero g₀ (surgeryOuterRadius_pos g₀ N) a
    map_smooth := dilatedSurgeryBallChart_contMDiffOn g₀ ha hR hfit
    inverse_smooth := (dilatedSurgeryBallInverse_contMDiff g₀ L a).contMDiffOn
    image_contains := dilatedSurgeryBallChart_image_contains g₀
      (surgeryOuterRadius_pos g₀ N) ha hR hfit H N.scale_pos hbeta
      (fun y => (surgeryMetric_radial_distance_bounds g₀ N hcut hsmall hC q hr y).1)
      hroom.le
    left_inverse := dilatedSurgeryBallChart_left_inverse g₀ ha hR hfit
    right_inverse := fun y _ => dilatedSurgeryBallChart_right_inverse g₀ ha y
    coefficient_smooth := dilatedSurgeryBallChart_coefficient_contDiffOn g₀ ha hR hfit H
    jets := ?_
  }⟩
  refine ⟨B0 * rho ^ 2, hbound, ?_⟩
  intro p hp
  have htensor : (fun x v => N.scale⁻¹ ^ 2 * surgeryCapPullback H f x v) =
      (fun x v => B x (v 0) (v 1)) := by
    funext x v
    rw [neck_scale_inverse_sq N]
    rfl
  rw [htensor]
  exact hcovariant U hU hKU B hBsmooth rho hrho.le p (hsourceK hp)
    (fun j hj => hjet p hp j hj)

end PoincareConjecture.M36
