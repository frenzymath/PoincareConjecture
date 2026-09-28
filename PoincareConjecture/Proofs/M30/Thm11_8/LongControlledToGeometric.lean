import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalVolume
import PoincareConjecture.Proofs.M30.Thm11_8.GeometricLongConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.LongSlabService











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



theorem geometricLongControls_of_longControlled
    {S : GeneralizedBlowupSequence.{u}} {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (H : LongControlledBlowupHypotheses S kappa r₀ T₀) :
    M30GeometricLongControls S T₀ := by
  classical
  have hcyl : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S k A T B eta) := by
    intro T hT hTT
    obtain ⟨B, hB, hfamily⟩ := H.cylinders T hT hTT
    refine ⟨B, hB, ?_⟩
    intro A hA eta heta
    filter_upwards [hfamily A hA eta heta] with k hk
    obtain ⟨E, _hnon⟩ := hk
    exact ⟨E⟩
  obtain ⟨T, hT0, hT, hTT⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp H.horizon_pos
  have hTpos : 0 < T := ENNReal.ofReal_pos.mp hT
  obtain ⟨B, hB, hfamily⟩ := H.cylinders T hTpos hTT
  let K : ℝ := max B 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  let d : ℝ := min 1 (min (Real.sqrt T) (Real.sqrt K)⁻¹)
  let rho : ℝ := d / 2
  let v : ℝ := kappa * rho ^ 3
  have hd : 0 < d := lt_min zero_lt_one
    (lt_min (Real.sqrt_pos.mpr hTpos) (inv_pos.mpr (Real.sqrt_pos.mpr hK)))
  have hrho : 0 < rho := half_pos hd
  have hrhod : rho ≤ d := by
    dsimp only [rho]
    linarith
  have hrho1 : rho ≤ 1 := hrhod.trans (min_le_left _ _)
  have hrhoT : rho ≤ Real.sqrt T :=
    hrhod.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrhoK : rho ≤ (Real.sqrt K)⁻¹ :=
    hrhod.trans ((min_le_right _ _).trans (min_le_right _ _))
  have htime : rho ^ 2 ≤ T := by
    calc
      rho ^ 2 ≤ (Real.sqrt T) ^ 2 := pow_le_pow_left₀ hrho.le hrhoT 2
      _ = T := Real.sq_sqrt hTpos.le
  have hcurv : B * rho ^ 2 ≤ 1 := by
    calc
      B * rho ^ 2 ≤ K * rho ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left B 1) (sq_nonneg rho)
      _ ≤ K * ((Real.sqrt K)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrho.le hrhoK 2) hK.le
      _ = 1 := by
        rw [inv_pow, Real.sq_sqrt hK.le, mul_inv_cancel₀ hK.ne']
  have hvolume : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1)
          (S.baseBall k rho) := by
    filter_upwards [hfamily 1 zero_lt_one 1 zero_lt_one,
      S.scalar_diverges.eventually_ge_atTop ((rho / r₀) ^ 2)] with k hk hlarge
    obtain ⟨E, hnon⟩ := hk
    have hbase : (S.base k).2 ∈ S.baseBall k 1 := by
      change ((S.flow k).metric (S.base k).1).edist (S.base k).2 (S.base k).2 <
        ENNReal.ofReal (1 / Real.sqrt (S.scale k))
      simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
      exact ENNReal.ofReal_pos.mpr
        (div_pos zero_lt_one (Real.sqrt_pos.mpr (S.base_scalar_pos k)))
    have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
    have hnonbase : GeneralizedKappaNoncollapsedAt
        (S.flow k) (S.base k) kappa r₀ := by
      simpa only [E.zero_identity hzero (S.base k).2 hbase] using
        hnon 0 hzero (S.base k).2 hbase
    have hsqrt : 0 < Real.sqrt (S.scale k) :=
      Real.sqrt_pos.mpr (S.base_scalar_pos k)
    have hcutoff : rho / Real.sqrt (S.scale k) ≤ r₀ := by
      apply (div_le_iff₀ hsqrt).mpr
      have h := (div_le_iff₀ H.radius_pos).mp
        (Real.le_sqrt_of_sq_le hlarge)
      simpa only [GeneralizedBlowupSequence.scale, mul_comm] using h
    have hv := terminal_volume_of_controlledCylinder E hnonbase
      hrho hrho1 htime hcurv hcutoff
    simpa only [v, div_pow, mul_div_assoc] using hv
  exact {
    horizon_pos := H.horizon_pos
    balls_compact := H.balls_compact
    terminal_volume := ⟨rho, v, hrho, mul_pos H.kappa_pos (pow_pos hrho 3), hvolume⟩
    cylinders := hcyl }





theorem geometricLongControls_of_m30LongControls
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon canonicalConstant kappa r₀ mu T₀)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hslab : M30LongSlabControlService S kappa r₀ T₀) :
    M30GeometricLongControls S T₀ := by
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound hC
      H.toM30CommonBlowupControls hbound
  exact {
    horizon_pos := H.horizon_pos
    balls_compact := H.balls_compact
    terminal_volume := ⟨rho, v, hrho, hv, hvolume⟩
    cylinders := by
      intro T hT hTT
      obtain ⟨B, hB, hfamily⟩ := Hslab.controlledBounds T hT hTT
      refine ⟨B, hB, ?_⟩
      intro A hA eta heta
      filter_upwards [hfamily A hA eta heta] with k hk
      obtain ⟨Tplus, hTplus, hTTplus, hTplusT₀, hE⟩ := hk
      exact hE }




theorem exists_geometric_long_of_longControlled
    (P : M30ControlledBlowupPredecessors.{u})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    {S : GeneralizedBlowupSequence.{u}} {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (H : LongControlledBlowupHypotheses S kappa r₀ T₀) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
  exact exists_geometric_long_generalizedBlowupConvergence P hMixed hFlow hSlice S
    (geometricLongControls_of_longControlled H)

end PoincareConjecture.M30
