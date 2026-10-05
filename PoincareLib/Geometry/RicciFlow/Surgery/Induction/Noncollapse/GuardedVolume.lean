import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseData
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.Transport.SurgeryCylinderRestriction

/-!
# Guarded tested volume from source noncollapsing

These are projections and time-window adapters of the positive-component-exempt
source predicate. They do not prove volume bounds on positive components or
produce the separate high-curvature analytic estimates.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

universe u

namespace PoincareMT

/-- The closed-cylinder volume test gives the same bound on a half-open
backward cylinder. Restrict to smaller radii and pass to the radius limit.
MT Definition 3.41, pp. 61-62, uses closed windows; Definitions 14.14-14.15,
p. 351, use half-open surgery windows. The positive-component exception from
Remark 16.2 is retained. No extension to the missing bottom time is assumed. -/
theorem SurgeryNoncollapsedOn.toIoc
    {F : SurgeryFlowData.{u}} {J : Set ℝ} {kappa : ℝ}
    (h : SurgeryNoncollapsedOn F J kappa) :
    ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
      ¬ SurgeryPositiveComponentAt F t x →
      ∀ r : ℝ, 0 < r → r ≤ F.parameters.epsilon →
      ∀ e : SurgeryFlowCylinder F (F.slice t) t 1
        (Ioc (-r ^ 2) 0) ((F.metric t).ball x r),
        (∀ hzero y, y ∈ (F.metric t).ball x r → HEq (e.forward 0 hzero y) y) →
        (∀ s hs y, y ∈ (F.metric t).ball x r →
          (F.connection (t + s / 1)).curvatureTensorNorm
            (e.forward s hs y) ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (kappa * r ^ 3) ≤
          calibratedMetricVolume (F.metric t) ((F.metric t).ball x r) := by
  intro t ht htF x hx r hr hre e hzero hcurv
  have hsmall (rho : ℝ) (hrho : rho ∈ Ioo 0 r) :
      ENNReal.ofReal (kappa * rho ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x r) := by
    have hsq : rho ^ 2 < r ^ 2 := by nlinarith [hrho.1, hrho.2]
    have hJ : Icc (-rho ^ 2) 0 ⊆ Ioc (-r ^ 2) 0 := by
      intro s hs
      exact ⟨by linarith [hs.1], hs.2⟩
    have hU : (F.metric t).ball x rho ⊆ (F.metric t).ball x r := by
      intro y hy
      exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hrho.2.le)
    have hscale : r⁻¹ ^ 2 ≤ rho⁻¹ ^ 2 := by
      gcongr <;> linarith [hrho.1, hrho.2]
    have hv := h t ht htF x hx rho hrho.1 (hrho.2.le.trans hre)
      (e.restrict hJ ordConnected_Icc hU)
      (fun hs y hy => hzero (hJ hs) y (hU hy))
      (fun s hs y hy => (hcurv s (hJ hs) y (hU hy)).trans hscale)
    exact hv.trans (measure_mono hU)
  have hlim : Tendsto (fun rho : ℝ => ENNReal.ofReal (kappa * rho ^ 3)) (𝓝[<] r)
      (𝓝 (ENNReal.ofReal (kappa * r ^ 3))) :=
    ENNReal.tendsto_ofReal
      ((continuous_const.mul (continuous_id.pow 3)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  apply le_of_tendsto hlim
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] r := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hpos] with rho hlt hpos'
  exact hsmall rho ⟨hpos', hlt⟩

theorem SurgeryNoncollapsedOn.testedVolumeOn
    {F : SurgeryFlowData.{u}} {J : Set ℝ} {kappa : ℝ}
    (h : SurgeryNoncollapsedOn F J kappa) (rBase B : ℝ) :
    SurgeryTestedVolumeOn F J kappa rBase B := by
  intro t ht htF x hx r hr hre e hzero hcurv
  exact h t ht htF x hx.1 r hr hre e hzero hcurv

/-! `SurgeryNoncollapsedAssumptionOn` uses the flow's parameter profile on
the volume lower bound, whereas the M46 output fixes the selected constant.
This adapter is valid only when that profile equality is supplied explicitly;
the equality is not inferred from canonical control. -/
theorem SurgeryNoncollapsedOn.toAssumptionOn
    {F : SurgeryFlowData.{u}} {J : Set ℝ} {kappa : ℝ}
    (h : SurgeryNoncollapsedOn F J kappa)
    (hκ : ∀ t ∈ J, t ∈ F.time_domain → F.parameters.kappa t = kappa) :
    SurgeryNoncollapsedAssumptionOn F J := by
  intro t ht htF x hx r hr hre e hzero hcurv
  have hv := h t ht htF x hx r hr hre e hzero hcurv
  simpa [hκ t ht htF] using hv

theorem SurgeryPrefixControls.oldTestedVolumeControls
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (h : SurgeryPrefixControls p F O) :
    OldTestedVolumeControls p F O := by
  exact (h.noncollapsed ⟨p.i, Nat.lt_succ_self _⟩ le_rfl).testedVolumeOn
    (p.r ⟨p.i, Nat.lt_succ_self _⟩) 16

/-- Apply the source extension on an ambient observation, then restrict the
resulting volume statement to the new epoch and B = 16. -/
theorem SurgeryNoncollapseExtension.testedVolume
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    (Q : SurgeryNoncollapseExtension.{u} p)
    (rNext : ℝ) (hr : 0 < rNext)
    (hrle : rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hnext : SurgeryObservationIsNextEpoch p O)
    (hprefix : SurgeryPrefixControls p F O)
    (hadmissible : SurgeryFlowAdmissible F)
    (hpinched : SurgeryFlowPinched F)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O rNext (Q.cutoff rNext))
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) rNext)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ Q.cutoff rNext) :
    SurgeryTestedVolumeOn F
      (surgeryObservationInterval O ∩ surgeryEpoch p.i)
      Q.kappaNew rNext 16 := by
  have h := (Q.noncollapsed rNext hr hrle F O hnext hprefix hadmissible
    hpinched terminal_policy scales canonical overlap).testedVolumeOn rNext 16
  intro t ht htF x hx r hrpos hre e hzero hcurv
  exact h t ht.1 htF x hx r hrpos hre e hzero hcurv

theorem SurgeryNoncollapseExtension.testedVolume_maximal
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    (Q : SurgeryNoncollapseExtension.{u} p)
    (rNext : ℝ) (hr : 0 < rNext)
    (hrle : rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hmax : SurgeryObservationIsMaximalNextEpoch p O)
    (hprefix : SurgeryPrefixControls p F O)
    (hadmissible : SurgeryFlowAdmissible F)
    (hpinched : SurgeryFlowPinched F)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O rNext (Q.cutoff rNext))
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) rNext)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ Q.cutoff rNext) :
    SurgeryTestedVolumeOn F
      (surgeryObservationInterval O ∩ surgeryEpoch p.i)
      Q.kappaNew rNext 16 :=
  Q.testedVolume rNext hr hrle F O hmax.1 hprefix hadmissible hpinched
    terminal_policy scales canonical overlap

/-- The maximal specialization keeps the domain equality visible next to the
checked projection.  This is the form needed by consumers that work directly
on the maximal flow domain rather than on the observation interval. -/
theorem SurgeryNoncollapseExtension.testedVolume_maximal_domain
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    (Q : SurgeryNoncollapseExtension.{u} p)
    (rNext : ℝ) (hr : 0 < rNext)
    (hrle : rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hmax : SurgeryObservationIsMaximalNextEpoch p O)
    (hprefix : SurgeryPrefixControls p F O)
    (hadmissible : SurgeryFlowAdmissible F)
    (hpinched : SurgeryFlowPinched F)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O rNext (Q.cutoff rNext))
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) rNext)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ Q.cutoff rNext) :
    SurgeryTestedVolumeOn F
      (F.time_domain ∩ surgeryEpoch p.i)
      Q.kappaNew rNext 16 := by
  have h := Q.testedVolume_maximal rNext hr hrle F O hmax hprefix
    hadmissible hpinched terminal_policy scales canonical overlap
  simpa [surgeryObservationInterval, hmax.2] using h

end PoincareMT
