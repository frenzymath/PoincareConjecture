import PoincareConjecture.Proofs.M36.ComparisonMetric
import PoincareConjecture.Proofs.M36.ComparisonWeightedJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem exists_comparison_domain_threshold (g₀ : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      m ≤ ⌊epsilon⁻¹⌋₊ ∧
      (∀ x ∈ K, standardSurgeryHeight g₀ x ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) ∧
      K ⊆ Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ epsilon)) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (standardSurgeryHeight_continuous g₀).continuousOn
  have hden : 0 < |B| + (m : ℝ) + 2 := by positivity
  refine ⟨1 / (|B| + (m : ℝ) + 2), one_div_pos.mpr hden, ?_⟩
  intro epsilon hepsilon hsmall
  have hinv := one_div_le_one_div_of_le hepsilon hsmall
  simp only [one_div, inv_inv] at hinv
  have hheight (x : StandardCapSpace) (hx : x ∈ K) :
      standardSurgeryHeight g₀ x ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    have hb : |standardSurgeryHeight g₀ x| ≤ |B| := by
      simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_abs_self B)
    have hab := abs_le.mp hb
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) m]
  refine ⟨(Nat.le_floor_iff (inv_pos.mpr hepsilon).le).mpr (by
    linarith [abs_nonneg B]), hheight, ?_⟩
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  apply (radialArclength_strictMono g₀).lt_iff_lt.mp
  rw [radialArclength_euclideanRadius]
  have hh := (hheight x hx).1
  dsimp [standardSurgeryHeight, surgeryOuterRadius, surgeryCapRadius] at *
  linarith only [hh]

set_option maxHeartbeats 800000 in


theorem exists_surgeryMetric_chart_jets_small (g₀ : StandardInitialMetric)
    (C q : ℝ) {r : ℝ} (hr : 0 < r)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
        (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹), N.epsilon ≤ delta →
      ∀ heta : 0 < 1 - 6 * N.epsilon,
      K ⊆ Metric.ball 0 (radialEuclideanRadius g₀ (surgeryOuterRadius g₀ N.epsilon)) ∧
      ∀ j : ℕ, j ≤ m → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (fun p => N.connection.scalarCurvature N.center •
          (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r
            N.scalar_center_pos heta hr).pullbackCoefficients
              (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)) p -
          g₀.metric.euclideanCoefficients p) x‖ ≤ tolerance := by
  let T := K ∩ tsupport (radialNeckWeight g₀)
  have hT : IsCompact T := hK.inter_right (isClosed_tsupport (radialNeckWeight g₀))
  obtain ⟨Cn, hCn, hneck⟩ := exists_comparisonNeckMetric_jet_bound g₀ hT
    (fun x hx => (radialNeckWeight_support_geometry g₀ hx.2).1)
    (fun x hx => (radialNeckWeight_support_geometry g₀ hx.2).2) m
  obtain ⟨A, hA, hweight⟩ := exists_radialWeightedError_jet_bound
    (F := E₃ →L[ℝ] E₃ →L[ℝ] ℝ) g₀ C q hr hK m
  obtain ⟨deltaD, hdD, hdomain⟩ := exists_comparison_domain_threshold g₀ hK m
  obtain ⟨d, hd, hscalar⟩ := Metric.eventually_nhds_iff.mp
    (standardScalarError_jets_eventually_small g₀ C q hr hK m
      (by linarith only [htolerance] : 0 < tolerance / 2))
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hCnpos : 0 < Cn := zero_lt_one.trans_le hCn
  refine ⟨min deltaD (min 1 (min (d / 2) (tolerance / (2 * A * Cn)))),
    lt_min hdD (lt_min zero_lt_one (lt_min (by positivity) (by positivity))), ?_⟩
  intro M _ _ _ g N hcut hsmall heta
  have heD := hsmall.trans (min_le_left _ _)
  have he1 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hed := hsmall.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have heb := hsmall.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨horder, hheight, hfit⟩ := hdomain N.epsilon N.epsilon_pos heD
  have hscalarbound := hscalar (by
    rw [Real.dist_eq, sub_zero, abs_of_pos N.epsilon_pos]
    linarith only [hed, hd] : dist N.epsilon 0 < d)
  let H := surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r
    N.scalar_center_pos heta hr
  let F := fun p => N.connection.scalarCurvature N.center •
    H.pullbackCoefficients (surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon)) p -
      g₀.metric.euclideanCoefficients p
  let B := fun p => (normalizedNeckMetric N).pullbackCoefficients
    (comparisonNeckLift g₀ N) p - g₀.metric.euclideanCoefficients p
  let W := fun p =>
    (radialConformalMultiplier g₀ C q N.epsilon r p * radialNeckWeight g₀ p) • B p
  let S := standardScalarError g₀ C q r N.epsilon
  have hBsmooth (x : StandardCapSpace) (hx : x ∈ T) : ContDiffAt ℝ ∞ B x :=
    ((normalizedNeckMetric N).contDiffAt_pullbackCoefficients
      (comparisonNeckLift_contMDiffAt g₀ N
        (radialNeckWeight_support_geometry g₀ hx.2).1 (hheight x hx.1))).sub
          (g₀.metric.contDiffAt_euclideanCoefficients x)
  have hWbound (j : ℕ) (hj : j ≤ m) (x : StandardCapSpace) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ j W x‖ ≤ tolerance / 2 := by
    apply (hweight N.epsilon ⟨N.epsilon_pos.le, he1⟩ B hBsmooth
      (Cn * N.epsilon) (mul_nonneg hCnpos.le N.epsilon_pos.le)
      (fun k hk y hy => hneck N horder (fun z hz => hheight z hz.1)
        y hy k hk) j hj x hx).trans
    have hb := (le_div_iff₀ (by positivity : 0 < 2 * A * Cn)).mp heb
    nlinarith only [hb]
  refine ⟨hfit, ?_⟩
  intro j hj x hx
  have hF : ContDiffAt ℝ ∞ F x :=
    ((H.contDiffAt_pullbackCoefficients
      ((surgeryBallChart_contMDiffOn g₀ _ x (hfit hx)).contMDiffAt
        (Metric.isOpen_ball.mem_nhds (hfit hx)))).const_smul
          (N.connection.scalarCurvature N.center)).sub
            (g₀.metric.contDiffAt_euclideanCoefficients x)
  have hS : ContDiffAt ℝ ∞ S x :=
    ((standardScalarError_joint_contDiff g₀ C q hr).comp
      (f := fun y : StandardCapSpace => (N.epsilon, y))
      (contDiff_const.prodMk contDiff_id)).contDiffAt
  have heq : F =ᶠ[nhds x] fun p => W p + S p := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (hfit hx)] with p hp
    exact surgeryMetric_chart_error g₀ N hcut C q r heta hr hp
  have hW : ContDiffAt ℝ ∞ W x := (hF.sub hS).congr_of_eventuallyEq (by
    filter_upwards [heq] with p hp
    change W p = F p - S p
    rw [hp, add_sub_cancel_right])
  change ‖iteratedFDeriv ℝ j F x‖ ≤ tolerance
  calc
    ‖iteratedFDeriv ℝ j F x‖ =
        ‖iteratedFDeriv ℝ j (fun p => W p + S p) x‖ := by
      rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    _ ≤ ‖iteratedFDeriv ℝ j W x‖ + ‖iteratedFDeriv ℝ j S x‖ := by
      change ‖iteratedFDeriv ℝ j (W + S) x‖ ≤ _
      rw [iteratedFDeriv_add_apply (i := j)
        (hW.of_le (by exact_mod_cast le_top))
        (hS.of_le (by exact_mod_cast le_top))]
      exact norm_add_le _ _
    _ ≤ tolerance := by
      exact (add_le_add (hWbound j hj x hx)
        (hscalarbound j hj x hx).le).trans_eq (by ring)

end PoincareConjecture.M36
