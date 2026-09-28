import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.UnitVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.BaseRadius











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance smallRadiusCarrierConnected (C : FlowCarrier.{0} 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)



theorem exists_small_radius_rescaled_sequence
    (P : M23NormalizedKappaCompactnessPredecessors) {ν : ℝ} (hν : 0 < ν)
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hvolume : ∀ k, calibratedMetricVolume ((S.term k).flow.flow.metric 0)
      (((S.term k).flow.flow.metric 0).ball (S.term k).base (ρ k)) =
        ENNReal.ofReal (ν * ρ k ^ 3)) :
    ∃ K : ∀ k, AncientKappaSolution 3 (S.term k).carrier.carrier,
      (∀ k, (K k).kappa = κ) ∧
      (∀ k t, MetricHomothetyCalculus
        ((S.term k).flow.flow.metric (ρ k ^ 2 * t)) ((K k).flow.metric t)
          (Diffeomorph.refl (𝓡 3) (S.term k).carrier.carrier ∞) ((ρ k)⁻¹ ^ 2)) ∧
      (∀ k, calibratedMetricVolume ((K k).flow.metric 0)
        (((K k).flow.metric 0).ball (S.term k).base 1) = ENNReal.ofReal ν) ∧
      (∀ k, ((K k).flow.connection 0).scalarCurvature (S.term k).base = ρ k ^ 2) ∧
      Tendsto (fun k ↦ ((K k).flow.connection 0).scalarCurvature (S.term k).base)
        atTop (𝓝 0) ∧
      ∀ r : ℝ, 0 < r → ∃ B : ℝ, 0 ≤ B ∧
        ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (S.term k).base r,
          |((K k).flow.connection t).curvatureTensorNorm x| ≤ B := by
  classical
  let Q (k : ℕ) : ℝ := (ρ k)⁻¹ ^ 2
  have hQ (k : ℕ) : 0 < Q k := sq_pos_of_pos (inv_pos.mpr (hρ k))
  let R (k : ℕ) : OrdinaryParabolicRescaling (I := closedAncientInterval)
      (S.term k).flow.flow (Q k) (hQ k) 0 :=
    Classical.choice (P.ordinary_rescaling (S.term k).carrier.carrier
      closedAncientInterval (S.term k).flow.flow (Q k) (hQ k) 0)
  let K (k : ℕ) : AncientKappaSolution 3 (S.term k).carrier.carrier :=
    (S.term k).flow.closedRescale (hQ k) (le_refl 0) (R k)
  have hkappa (k : ℕ) : (K k).kappa = κ := (S.term k).kappa_eq
  have hcal (k : ℕ) (t : ℝ) : MetricHomothetyCalculus
      ((S.term k).flow.flow.metric (ρ k ^ 2 * t)) ((K k).flow.metric t)
        (Diffeomorph.refl (𝓡 3) (S.term k).carrier.carrier ∞) ((ρ k)⁻¹ ^ 2) := by
    have h := (S.term k).flow.closedRescale_metric_calculus (hQ k) (le_refl 0) (R k) t
    have hclock : (0 : ℝ) + t / Q k = ρ k ^ 2 * t := by
      simp only [Q, div_eq_mul_inv, inv_pow, inv_inv, zero_add, mul_comm]
    rw [hclock] at h
    exact h
  have hunit (k : ℕ) : calibratedMetricVolume ((K k).flow.metric 0)
      (((K k).flow.metric 0).ball (S.term k).base 1) = ENNReal.ofReal ν := by
    have H := hcal k 0
    rw [mul_zero] at H
    change MetricHomothetyCalculus ((S.term k).flow.flow.metric 0) ((K k).flow.metric 0)
      (Diffeomorph.refl (𝓡 3) (S.term k).carrier.carrier ∞) (Q k) at H
    have hsqrt : Real.sqrt (Q k) = (ρ k)⁻¹ := Real.sqrt_sq (inv_nonneg.mpr (hρ k).le)
    have hrad : Real.sqrt (Q k) * ρ k = 1 := by
      rw [hsqrt, inv_mul_cancel₀ (hρ k).ne']
    have hball : ((S.term k).flow.flow.metric 0).ball (S.term k).base (ρ k) =
        ((K k).flow.metric 0).ball (S.term k).base 1 := by
      simpa only [Diffeomorph.coe_refl, id_eq, image_id', hrad] using
        H.ball_image (S.term k).base (ρ k)
    have hv := H.volume_image (((S.term k).flow.flow.metric 0).ball (S.term k).base (ρ k))
    change calibratedMetricVolume ((K k).flow.metric 0)
      (id '' ((S.term k).flow.flow.metric 0).ball (S.term k).base (ρ k)) =
        ENNReal.ofReal (Real.rpow (Q k) ((3 : ℝ) / 2)) *
          calibratedMetricVolume ((S.term k).flow.flow.metric 0)
            (((S.term k).flow.flow.metric 0).ball (S.term k).base (ρ k)) at hv
    rw [image_id, hvolume k, hball] at hv
    have hscale : Real.rpow (Q k) ((3 : ℝ) / 2) = (ρ k)⁻¹ ^ 3 := by
      rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt _ (hQ k).le,
        hsqrt, Real.rpow_ofNat]
    change _ = ENNReal.ofReal (Real.rpow (Q k) ((3 : ℝ) / 2)) *
      ENNReal.ofReal (ν * ρ k ^ 3) at hv
    rw [hscale, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr (hρ k).le) 3)] at hv
    have hcancel : (ρ k)⁻¹ ^ 3 * (ν * ρ k ^ 3) = ν := by
      calc
        (ρ k)⁻¹ ^ 3 * (ν * ρ k ^ 3) = ν * ((ρ k)⁻¹ * ρ k) ^ 3 := by ring
        _ = ν := by rw [inv_mul_cancel₀ (hρ k).ne', one_pow, mul_one]
    rwa [hcancel] at hv
  have hscalar (k : ℕ) :
      ((K k).flow.connection 0).scalarCurvature (S.term k).base = ρ k ^ 2 := by
    rw [(S.term k).flow.closedRescale_scalar]
    rw [show (0 : ℝ) + 0 / Q k = 0 by simp, (S.term k).scalar_normalized]
    simp only [Q, one_div, inv_pow, inv_inv]
  refine ⟨K, hkappa, hcal, hunit, hscalar, ?_, ?_⟩
  · have heq : (fun k ↦ ((K k).flow.connection 0).scalarCurvature (S.term k).base) =
        (fun k ↦ ρ k ^ 2) := funext hscalar
    rw [heq]
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hρlim.pow 2
  · intro r hr
    obtain ⟨B, hB, hbound⟩ :=
      m23_exists_local_curvature_bound_of_unit_ball_volume P S.kappa_pos hν hr
    exact ⟨B, hB, fun k ↦ hbound (S.term k).carrier (K k) (hkappa k)
      (S.term k).base (hunit k).ge⟩



theorem exists_small_radius_rescaled_sequence_of_not_localCurvatureEstimate
    (P : M23NormalizedKappaCompactnessPredecessors) (hn : ¬ M23LocalCurvatureEstimate S) :
    ∃ (j : ℕ → ℕ) (ρ : ℕ → ℝ)
      (K : ∀ k, AncientKappaSolution 3 (S.term (j k)).carrier.carrier),
      (∀ k, 0 < ρ k) ∧ Tendsto ρ atTop (𝓝 0) ∧ (∀ k, (K k).kappa = κ) ∧
      (∀ k t, MetricHomothetyCalculus
        ((S.term (j k)).flow.flow.metric (ρ k ^ 2 * t)) ((K k).flow.metric t)
          (Diffeomorph.refl (𝓡 3) (S.term (j k)).carrier.carrier ∞) ((ρ k)⁻¹ ^ 2)) ∧
      (∀ k, calibratedMetricVolume ((K k).flow.metric 0)
        (((K k).flow.metric 0).ball (S.term (j k)).base 1) =
          ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 / 2)) ∧
      (∀ k, ((K k).flow.connection 0).scalarCurvature (S.term (j k)).base = ρ k ^ 2) ∧
      Tendsto (fun k ↦ ((K k).flow.connection 0).scalarCurvature (S.term (j k)).base)
        atTop (𝓝 0) ∧
      ∀ r : ℝ, 0 < r → ∃ B : ℝ, 0 ≤ B ∧
        ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (S.term (j k)).base r,
          |((K k).flow.connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨j, ρ, hρ, hρlim⟩ := S.exists_half_euclidean_radii_of_not_localCurvatureEstimate P hn
  let T : NormalizedKappaSolutionSequence κ := ⟨S.kappa_pos, fun k ↦ S.term (j k)⟩
  obtain ⟨K, hkappa, hcal, hunit, hscalar, hscalarlim, hcontrol⟩ :=
    T.exists_small_radius_rescaled_sequence P
      (half_pos (RiemannianMetric.euclideanUnitBallVolume_pos 3))
      ρ (fun k ↦ (hρ k).1) hρlim (fun k ↦ (hρ k).2)
  exact ⟨j, ρ, K, fun k ↦ (hρ k).1, hρlim, hkappa, hcal, hunit, hscalar, hscalarlim, hcontrol⟩

end PoincareConjecture.NormalizedKappaSolutionSequence
