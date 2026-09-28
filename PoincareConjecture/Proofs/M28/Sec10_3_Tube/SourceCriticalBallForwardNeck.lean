import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallForwardGeometry
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallForwardMetricError
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialCoefficients
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.ForwardCoreCoefficientReadout
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.RawError











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube PoincareConjecture.Proofs.M28.NeckTransfer PoincareConjecture.Proofs.M28.NeckAnalysis

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 2400000 in





theorem eventually_exists_regularRawStage_forward_neck (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j : ℕ), L.carrier ⊆ G.exhaustion j →
      L.center = G.base → L.scale = (4 * max C 2)⁻¹ →
      ∀ theta : ℝ, L.epsilon < theta → theta < 1 / 2 →
        ∀ᶠ k in atTop, ∃ N : EpsilonNeck
          ((E (phi (G.subsequence k) + H.shift)).flow.metric
            (E (phi (G.subsequence k) + H.shift)).time),
          N.epsilon = theta ∧
          N.center = ((T (phi (G.subsequence k))).list.node 0).2.center ∧
          N.scale = ((T (phi (G.subsequence k))).list.node 0).2.scale ∧
          N.connection = ((T (phi (G.subsequence k))).list.node 0).2.connection ∧
          N.carrier = (H.regularRawStageDiffeomorph T A1 hA1 phi G k) ''
            L.region (-theta⁻¹) theta⁻¹ ∧
          N.central_sphere = (H.regularRawStageDiffeomorph T A1 hA1 phi G k) ''
            L.central_sphere ∧
          ∀ z : RoundCylinderSpace, N.coordinate_map z =
            H.regularRawStageDiffeomorph T A1 hA1 phi G k (L.coordinate_map z) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro L j hLstage hLcenter hLscale theta htheta hhalf
  let m := ⌊theta⁻¹⌋₊
  have htheta_pos : 0 < theta := L.epsilon_pos.trans htheta
  have hmpos : 1 ≤ m := (Nat.one_le_floor_iff _).mpr
    ((one_le_inv₀ htheta_pos).mpr (by linarith))
  obtain ⟨n, hnm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hn : n + 1 ≤ ⌊L.epsilon⁻¹⌋₊ := by
    have horder : m ≤ ⌊L.epsilon⁻¹⌋₊ := cylinderOrder_mono L.epsilon_pos htheta.le
    omega
  obtain ⟨delta, hdelta, hperturb⟩ :=
    exists_roundCylinderClose_perturbation_tolerance L.epsilon_pos htheta
  obtain ⟨rho, hrho, hraw⟩ := exists_cylinder_raw_error_tolerance m hdelta
  let J := cylinderScalarCoordinateEquiv.symm.toContinuousLinearMap
  let F := L.scale⁻¹ ^ 2 * (max 1 ‖J‖) ^ m
  have hF : 0 < F := mul_pos (pow_pos (inv_pos.mpr L.scale_pos) 2)
    (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) m)
  obtain ⟨K, hK⟩ := H.exists_regularRawStage_forward_metric_error T A1 hA1 phi G
    L j hLstage n hn (rho / F) (div_pos hrho hF)
  filter_upwards [eventually_ge_atTop j, eventually_ge_atTop K] with k hjk hkK
  obtain ⟨V, hcenter, hscale, hconnection, hcarrier, hsphere, hmap⟩ :=
    H.exists_regularRawStage_forward_neck_geometry T A1 hA1 phi G L j hLstage
      hLcenter theta htheta.le hhalf k hjk
  let i := phi (G.subsequence k)
  let Q := (E (i + H.shift)).flow.scalar
    ⟨(E (i + H.shift)).time, (E (i + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos i
  have hscaleQ : Q * V.scale ^ 2 = L.scale ^ 2 := by
    rw [hscale, hLscale]
    exact H.normalizedSlice_initial_scale_sq T i
  let S : RoundCylinderTwoTensor := fun z v w =>
    L.scale⁻¹ ^ 2 * roundCylinderPullback G.limitMetric L.coordinate_map z v w
  have hsource : RoundCylinderClose L.epsilon 0 S := L.metric_comparison.close
  have hclose : RoundCylinderClose theta 0 V.tensor := by
    apply hperturb 0 (by norm_num) V.tensor S hsource V.tensor_smooth
    intro z hz
    apply hraw theta V.tensor S V.tensor_smooth
      (hsource.1.mono_epsilon_m28 L.epsilon_pos htheta.le) z hz
    intro r hr a b
    have hsL := cylinderStrip_mono L.epsilon_pos htheta.le hz
    have h := V.norm_frozen_forward_difference_jet_le L Q hQ hscaleQ z.1 hz hsL a b r
    have hlocal : V.coordinate_map ∘
        (cylinderSphereParametrization z.1 ∘ cylinderScalarCoordinates z.2) =
          H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘ cylinderNeckChart L z.1 z.2 := by
      funext x
      exact hmap _
    rw [hlocal] at h
    have hmetric : ‖iteratedFDeriv ℝ r (fun x =>
        RiemannianMetric.pullbackCoefficients
          (M13.scaleSmoothMetric ((E (i + H.shift)).flow.metric
            (E (i + H.shift)).time) Q hQ)
          (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘ cylinderNeckChart L z.1 z.2) x -
        G.limitMetric.pullbackCoefficients (cylinderNeckChart L z.1 z.2) x) 0‖ ≤ rho / F :=
      hK k hkK z hsL r (by omega)
    have hpower : ‖J‖ ^ r ≤ (max 1 ‖J‖) ^ m :=
      (pow_le_pow_left₀ (norm_nonneg J) (le_max_right _ _) r).trans
        (pow_le_pow_right₀ (le_max_left _ _) hr)
    have hfactor : L.scale⁻¹ ^ 2 * ‖J‖ ^ r ≤ F :=
      mul_le_mul_of_nonneg_left hpower (sq_nonneg _)
    exact h.trans ((mul_le_mul_of_nonneg_left hmetric
      (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))).trans
        ((mul_le_mul_of_nonneg_right hfactor (div_pos hrho hF).le).trans_eq
          (mul_div_cancel₀ rho hF.ne')))
  exact ⟨V.toEpsilonNeck hclose, rfl, hcenter, hscale, hconnection, hcarrier, hsphere, hmap⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
