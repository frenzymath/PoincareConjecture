import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialPastComparison
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialActualCoefficients
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCenteredJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem exists_source_initial_native_past_bound (P : M47Predecessors.{u})
    {zeta K : ℝ} (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ 1 / 8)
    (hK : 0 < K) (m : ℕ) :
    ∃ Cerror Lerror Kmodel : ℝ, 0 < Cerror ∧ 0 ≤ Lerror ∧ 0 ≤ Kmodel ∧
      ∀ {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
      {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
      {T q left R : ℝ}, R + 1 < N.epsilon⁻¹ →
      m ≤ ⌊N.epsilon⁻¹⌋₊ → left ≤ -1 - 4 * zeta →
      ∀ (U : TopologicalSpace.Opens C.carrier),
      (U : Set C.carrier) = N.region (-(R + 1)) (R + 1) →
      (U : Set C.carrier).Nonempty →
      ∀ (D : SurgeryFlowCylinder F C T q (Icc left (-1 / 2)) U)
        (old : SurgeryFlowCylinder F C T q (Ioo (-1 : ℝ) 0) N.carrier),
      (∀ v (hv : v ∈ Icc left (-1 / 2)) (hraw : v ∈ Ioo (-1 : ℝ) 0),
        ∀ x ∈ U, D.forward v hv x = old.forward v hraw x) →
      (∀ v ∈ Ioo (-1 : ℝ) 0,
        RoundCylinderClose N.epsilon v (surgeryCylinderPullback old N.coordinate_map v)) →
      (∀ v (hv : v ∈ Icc left (-1 / 2)),
        v ∈ Icc (-1 - 4 * zeta) (-1 + zeta) → ∀ x ∈ U,
          (F.connection (T + v / q)).curvatureTensorNorm (D.forward v hv x) ≤ K * q) →
      ∀ {omega : ℝ}, 0 ≤ omega → omega ≤ zeta / 2 →
      ∀ v ∈ Icc (-1 - omega) (-1 : ℝ),
      ∀ (theta : UnitTwoSphere) (c : ℝ), |c| ≤ R →
        roundCylinderJetErrorSquared v (surgeryCylinderPullback D N.coordinate_map v)
          m (theta, c) ≤ Kmodel * (Cerror * N.epsilon + Lerror * omega) ^ 2 := by
  obtain ⟨Cerror, Lerror, hCerror, hLerror, hcomparison⟩ :=
    exists_source_initial_past_comparison P hzeta hzetaSmall hK m
  obtain ⟨Kmodel, hKmodel, henergy⟩ := exists_source_initial_centered_native_bound m
  refine ⟨Cerror, Lerror, Kmodel, hCerror, hLerror, hKmodel, ?_⟩
  intro F C g N T q left R hbuffer horder hleft U hU hne D old hagreement hclose hcurv
  obtain ⟨hmem, G, hread, _hGcurv, hcharts⟩ :=
    hcomparison N hbuffer horder hleft U hU hne D old hagreement hclose hcurv
  intro omega homega homegaSmall v hv theta c hc
  let s : ℝ := v + 1 - zeta
  have hs : s ∈ Icc (-zeta - omega) (-zeta) := by
    dsimp only [s]
    constructor <;> linarith only [hv.1, hv.2]
  have hslab : s ∈ Icc (-(5 * zeta)) 0 := by
    constructor <;> linarith only [hs.1, hs.2, homegaSmall, hzeta]
  have hraw : -1 + zeta + s = v := by dsimp only [s]; ring
  obtain ⟨Phi, hsource, hmap, _hold, hjets⟩ := hcharts theta c hc
  have hdomain : Metric.ball (0 : E) (1 / 2) ⊆ centeredNeckDomain N c := by
    intro p hp
    have hp' : ‖p‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hp
    have hheight : |cylinderHeightCovector p| ≤ ‖p‖ := by
      change |p 2| ≤ ‖p‖
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p (2 : Fin 3)
    apply abs_lt.mp
    exact (abs_add_le _ _).trans_lt (by linarith only [hheight, hp', hc, hbuffer])
  have hcoeff : (G.metric s).pullbackCoefficients Phi =ᶠ[𝓝 (0 : E)]
      centeredCylinderMetric (surgeryCylinderPullback D N.coordinate_map v) theta c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))] with p hp
    have h := source_initial_actual_slab_coefficients N U D (-1 + zeta + s)
      (hmem hslab) (G.metric s) (fun x => (hread s hslab x).1)
      theta c Phi hsource hmap hdomain hp
    simpa only [hraw] using h
  have hzero : (0 : E) ∈ Phi.source := by
    rw [hsource]
    exact Metric.mem_ball_self (by norm_num)
  have hPhi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ Phi (0 : E) :=
    Phi.contMDiffOn.contMDiffAt (Phi.open_source.mem_nhds hzero)
  have hB : ContDiffAt ℝ ∞
      (centeredCylinderMetric (surgeryCylinderPullback D N.coordinate_map v) theta c)
      (0 : E) :=
    ((G.metric s).contDiffAt_pullbackCoefficients hPhi).congr_of_eventuallyEq hcoeff.symm
  apply henergy (by linarith only [hv.2] : v ≤ 0)
    (surgeryCylinderPullback D N.coordinate_map v) theta c hB
    (Cerror * N.epsilon + Lerror * omega)
    (add_nonneg (mul_nonneg hCerror.le N.epsilon_pos.le) (mul_nonneg hLerror homega))
  intro j hj
  have h := hjets homega homegaSmall s hs j hj
  rw [(hcoeff.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds] at h
  simpa only [hraw] using h

end PoincareConjecture.M47
