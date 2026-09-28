import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTipCapture
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialTipObstruction
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCapPath










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open M45



theorem source_initial_compared_cap_no_contact
    {F : SurgeryFlowData.{u}} (standard : RepairedStandardCapExistenceData F.standard_initial)
    {C : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 C.carrier}
    (N : EpsilonNeck g) {origin scale : ℝ} {I : Set ℝ}
    (old : SurgeryFlowCylinder F C origin scale I N.carrier)
    (hsmall : N.epsilon ≤ 1 / 1200)
    (u : ℝ) (hu : u ∈ I) (hutime : u ∈ Ioo (-1 : ℝ) 0)
    (hclose : RoundCylinderClose N.epsilon u (surgeryCylinderPullback old N.coordinate_map u))
    {R mu K : ℝ} (hR : 0 ≤ R) (hmu : 0 < mu) (hK : 0 < K)
    (haccuracy : N.epsilon ≤
      1 / (R + 2 + 4 * (4 * (F.standard_initial.cylindrical_end.radius + 5)) * Real.sqrt K))
    (htolerance : N.epsilon ≤ mu / (1024 * (K + 1)))
    {t : ℝ} {hT : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    {i : Fin (F.event t hT).cap_count} {A eta : ℝ}
    (hA : 2 * (F.standard_initial.cylindrical_end.radius + 5) < A)
    {J : Set ℝ}
    (cap : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
      ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F standard.flow A eta cap initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (hbase : ∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
      HEq (cap.forward 0 hzero y) y)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    (sigma : ℝ) (hsigma : sigma ∈ J)
    {y : (F.slice t).carrier} (hy : y ∈ ((F.event t hT).caps i).carrier)
    {x : C.carrier} (hx : x ∈ N.region (-R) R)
    (hcontact : (⟨t + sigma / ((F.parameters.h t)⁻¹ ^ 2), cap.forward sigma hsigma y⟩ :
      Σ r, (F.slice r).carrier) = ⟨origin + u / scale, old.forward u hu x⟩)
    (hupper : (F.parameters.h t) ^ 2 *
      (F.connection (t + sigma / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
        (cap.forward sigma hsigma y) ≤ K)
    (htip : ∀ w : TangentSpace (𝓡 3) (cap.forward sigma hsigma ((F.event t hT).caps i).tip),
      (mu / (F.parameters.h t) ^ 2) *
        (F.metric (t + sigma / ((F.parameters.h t)⁻¹ ^ 2))).inner
          (cap.forward sigma hsigma ((F.event t hT).caps i).tip) w w ≤
        (F.connection (t + sigma / ((F.parameters.h t)⁻¹ ^ 2))).ricci
          (cap.forward sigma hsigma ((F.event t hT).caps i).tip) w w) : False := by
  let h := F.parameters.h t
  let D := 4 * (F.standard_initial.cylindrical_end.radius + 5)
  let r := (F.connection (origin + u / scale)).scalarCurvature (old.forward u hu x)
  have herr : |r / scale - 1 / (1 - u)| ≤ (16 / 5 : ℝ) * N.epsilon :=
    source_neck_slice_scalar_difference_le N old
      (show N.epsilon ≤ 1 / 200 by linarith only [hsmall]) u hu hutime.2.le hclose hx.1
  have hden : 0 < 1 - u := by linarith only [hutime.2]
  have hmodel : (1 / 2 : ℝ) < 1 / (1 - u) :=
    (lt_div_iff₀ hden).mpr (by linarith only [hutime.1])
  have hlow : (1 / 4 : ℝ) < r / scale := by
    have h := (abs_le.mp herr).1
    linarith only [h, hmodel, hsmall]
  have hphysical : scale / 4 ≤ r := by
    have h := (lt_div_iff₀ old.scale_pos).mp hlow
    linarith only [h]
  have hscalarEq := congrArg
    (fun p : Σ r, (F.slice r).carrier => (F.connection p.1).scalarCurvature p.2) hcontact
  have hupper' : h ^ 2 * r ≤ K := by
    change h ^ 2 * _ ≤ K at hupper
    change _ = r at hscalarEq
    rwa [hscalarEq] at hupper
  have hscale : scale * h ^ 2 ≤ 4 * K := by
    have h := mul_le_mul_of_nonneg_left hphysical (sq_nonneg h)
    nlinarith only [h, hupper']
  obtain ⟨gamma, hgamma, hstart, hend, _himage, hlength⟩ :=
    source_initial_cap_contact_path standard hA cap initial comparison hzero hbase
      hh heta hetaSmall sigma hsigma hy

  let HasTipPath (p : Σ r, (F.slice r).carrier) : Prop :=
    ∃ path : ℝ → (F.slice p.1).carrier,
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 path (Icc 0 1) ∧ path 0 = p.2 ∧
      (F.metric p.1).pathELength path 0 1 < ENNReal.ofReal (D * h) ∧
      ∀ w : TangentSpace (𝓡 3) (path 1),
        (mu / h ^ 2) * (F.metric p.1).inner (path 1) w w ≤
          (F.connection p.1).ricci (path 1) w w
  have hpath : HasTipPath
      ⟨t + sigma / ((F.parameters.h t)⁻¹ ^ 2), cap.forward sigma hsigma y⟩ := by
    refine ⟨gamma, hgamma, hstart, hlength, ?_⟩
    rw [hend]
    exact htip
  have holdPath : HasTipPath ⟨origin + u / scale, old.forward u hu x⟩ := hcontact ▸ hpath
  obtain ⟨path, hpathSmooth, hpathStart, hpathLength, hpathTip⟩ := holdPath
  have hD : 0 < D := by
    have hA0 := F.standard_initial.cylindrical_end.radius_pos
    dsimp only [D]
    positivity
  have hcapture := source_neck_slice_cap_length_capture N old
    (show N.epsilon ≤ 1 / 2 by linarith only [hsmall]) u hu hutime.2.le hclose
    hK hD hh hR hscale haccuracy path hpathSmooth hx hpathStart hpathLength
  exact source_neck_slice_not_tip_ricci_lower N old hsmall u hu hutime.2.le hclose
    hmu hK hh hscale htolerance (hcapture ⟨zero_le_one, le_rfl⟩) hpathTip

end PoincareConjecture.M47
