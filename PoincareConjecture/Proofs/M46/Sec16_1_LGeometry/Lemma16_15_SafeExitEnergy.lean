import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_InverseEnergy
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_EntryFrontier
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_FirstExitCompletion
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_SideAction
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_PositiveSquareEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12




theorem actualSafeCylinder_exit_energy
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) {rho : ℝ} (hrho : 0 < rho)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val),
      scale * ((1 / 2 : ℝ) * gBirth.inner z.val v v) ≤ e.pullbackInner s hs z.val v v)
    (center : C.carrier) (hsource : (U : Set C.carrier) = gBirth.ball center (rho / 2))
    {T tau b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (hb : 0 < b) (hbtau : b ≤ Real.sqrt tau)
    (himage : MapsTo (fun s => p.curve (s ^ 2)) (Ioo 0 b)
      (range (rawCylinderMap G.realization e)))
    (hbclock : G.realization.spacetime.timeFunction (p.curve (b ^ 2)) ∈
      (cylinderPhysicalInterval origin scale e.scale_pos J).domain)
    (hout : p.curve (b ^ 2) ∉ range (rawCylinderMap G.realization e))
    (z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hbase : p.curve 0 = rawCylinderMap G.realization e z) (hcenter : z.2.val = center) :
    rho ^ 2 / (16 * b) ≤ ∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t := by
  have hsub : Ioo 0 b ⊆ Ioo (Real.sqrt 0) (Real.sqrt tau) := by
    simpa only [Real.sqrt_zero] using Ioo_subset_Ioo le_rfl hbtau
  obtain ⟨beta, heq, _, hregular, hclock, henergy⟩ :=
    exists_rawCylinder_energy_lift G e hI gBirth (1 / 2) hbound (nonempty_Ioo.mpr hb)
      isOpen_Ioo ((M14.squarePath_contMDiffOn p).mono hsub) himage
  have hpoint : ∀ s ∈ Ioo 0 b,
      (1 / 2 : ℝ) * M08.referenceSpeedSq gBirth (fun r => (beta r).2.val) s ≤
        M14.pathSquareKinetic p s := by
    intro s hs
    have h := henergy s hs
    change (1 / 2 : ℝ) * M08.referenceSpeedSq gBirth (fun r => (beta r).2.val) s ≤
      G.toLGeometry.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
        (M14.projectedCurveVelocity G.toLGeometry (fun r => p.curve (r ^ 2)) s)
        (M14.projectedCurveVelocity G.toLGeometry (fun r => p.curve (r ^ 2)) s) at h
    rw [M14.squarePath_projectedVelocity p (hsub hs)] at h
    exact h
  have hk : IntervalIntegrable (M14.pathSquareKinetic p) volume 0 b := by
    have hfull := M14.squarePath_kinetic_intervalIntegrable p hM12
    simp only [Real.sqrt_zero] at hfull
    apply hfull.mono_set
    rw [uIcc_of_le hb.le, uIcc_of_le (Real.sqrt_nonneg tau)]
    exact Icc_subset_Icc le_rfl hbtau
  obtain ⟨hfinite, hkinetic⟩ := birthEnergy_integrable_of_action_bound gBirth hb.le
    (by norm_num : (0 : ℝ) < 1 / 2) hregular (M14.pathSquareKinetic p) hk hpoint
  obtain ⟨xi, hxi, hsame, hxiRegular, hxiEnergy, hintegral⟩ :=
    exists_continuous_birthCurve_extension gBirth hb hregular hfinite
  have hpcont : ContinuousOn (fun s => p.curve (s ^ 2)) (Icc 0 b) := by
    apply (M14.squarePath_continuousOn p).mono
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Icc_subset_Icc le_rfl hbtau
  have hcoordinate : EqOn (fun t => (beta t).2.val) xi (Ioo 0 b) := hsame.symm
  have hstart : xi 0 = center := by
    have hstartRaw : p.curve ((0 : ℝ) ^ 2) = rawCylinderMap G.realization e z := by
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hbase
    exact (rawCylinder_completed_coordinate_eq G.realization e hb ⟨le_rfl, hb.le⟩
      hpcont hxi.continuousOn beta heq hcoordinate z hstartRaw).trans hcenter
  have houter : xi b ∉ gBirth.ball center (rho / 2) := by
    intro hx
    have hxU : xi b ∈ U := by
      change xi b ∈ (U : Set C.carrier)
      rwa [hsource]
    exact hout ⟨_, (rawCylinder_completed_endpoint_eq G.realization e hb ⟨hb.le, le_rfl⟩
      hpcont hxi.continuousOn beta heq hcoordinate hclock hbclock hxU).symm⟩
  have hsep : ENNReal.ofReal (rho / 2) ≤ gBirth.edist (xi 0) (xi b) := by
    rw [hstart]
    exact le_of_not_gt houter
  have hdist := sq_distance_le_duration_mul_energy gBirth hb (by positivity)
    hxi.continuousOn hxiRegular hxiEnergy hsep
  rw [sub_zero, hintegral] at hdist
  have hpositive := pathSquareKinetic_prefix_le_positiveAction hM12 p hb.le hbtau
  apply (div_le_iff₀ (by positivity : 0 < 16 * b)).mpr
  nlinarith

end PoincareConjecture.Proofs.M46
