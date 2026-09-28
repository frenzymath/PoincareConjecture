import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderTailEnergy
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedReparameterization
import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift
import PoincareConjecture.Proofs.M14.Sec6_2_SquareCurve










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
  {C : GeneralizedSliceCarrier.{u}} {T tau d rho Q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}



theorem exists_seed_cylinder_tail (htau : 0 < tau) (hd : 0 < d) (hrho : 0 ≤ rho)
    (hJ : J.domain = Icc (-d) 0)
    (e : GeneralizedFlowCylinder F C (T - tau) 1 J.domain U)
    (hI : (cylinderPhysicalInterval (T - tau) 1 e.scale_pos J).domain ⊆ F.interval)
    (gSource : RiemannianMetric 3 C.carrier)
    (hmetric : ∀ s hs (x : U) (v : TangentSpace (𝓡 3) x.val),
      e.pullbackInner s hs x.val v v ≤ 2 * gSource.inner x.val v v)
    (hscalar : ∀ s hs (x : U),
      horizontalScalarCurvature G.toLGeometry.leafwise (e.pointMap s hs x.val) ≤ Q)
    (alpha : ℝ → C.carrier) (halpha : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 alpha)
    (hsource : MapsTo alpha (Icc (0 : ℝ) 1) U)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1, M04.pathSpeed gSource alpha s ≤ 2 * rho) :
    ∃ beta : ℝ → G.toLGeometry.Point,
      ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 beta
        (Icc (Real.sqrt tau) (Real.sqrt (tau + d))) ∧
      (∀ s ∈ Icc (Real.sqrt tau) (Real.sqrt (tau + d)),
        G.toLGeometry.spacetime.timeFunction (beta s) = T - s ^ 2) ∧
      (∀ hzero : 0 ∈ J.domain,
        beta (Real.sqrt tau) = e.pointMap 0 hzero (alpha 0)) ∧
      (∀ hleft : -d ∈ J.domain,
        beta (Real.sqrt (tau + d)) = e.pointMap (-d) hleft (alpha 1)) ∧
      ∀ s ∈ Ioo (Real.sqrt tau) (Real.sqrt (tau + d)),
        M14.squareCurveDensity G.toLGeometry beta
          (Icc (Real.sqrt tau) (Real.sqrt (tau + d))) s ≤
            2 * s ^ 2 * (Q + 8 * rho ^ 2 / d ^ 2) := by
  classical
  let K := Icc (Real.sqrt tau) (Real.sqrt (tau + d))
  have htd : 0 < tau + d := add_pos htau hd
  have horder : Real.sqrt tau < Real.sqrt (tau + d) :=
    Real.sqrt_lt_sqrt htau.le (lt_add_of_pos_right _ hd)
  have hsq (s : ℝ) (hs : s ∈ K) : tau ≤ s ^ 2 ∧ s ^ 2 ≤ tau + d := by
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg tau).trans hs.1
    constructor
    · rw [← Real.sq_sqrt htau.le]
      exact (sq_le_sq₀ (Real.sqrt_nonneg tau) hs0).mpr hs.1
    · rw [← Real.sq_sqrt htd.le]
      exact (sq_le_sq₀ hs0 (Real.sqrt_nonneg (tau + d))).mpr hs.2
  have hparam (s : ℝ) (hs : s ∈ K) : tau - s ^ 2 ∈ J.domain := by
    rw [hJ]
    constructor <;> linarith [(hsq s hs).1, (hsq s hs).2]
  have hunit (s : ℝ) (hs : s ∈ K) : (s ^ 2 - tau) / d ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr (hsq s hs).1) hd.le,
      (div_le_one hd).mpr (by linarith [(hsq s hs).2])⟩
  have hzero : 0 ∈ J.domain := by rw [hJ]; exact ⟨by linarith, le_rfl⟩
  let localTime (s : ℝ) : J.domain :=
    if hs : s ∈ K then ⟨tau - s ^ 2, hparam s hs⟩ else ⟨0, hzero⟩
  let theta (s : ℝ) : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval (T - tau) 1 e.scale_pos J)).Point :=
    (cylinderClockHomeomorph (T - tau) 1 e.scale_pos J).symm (localTime s)
  let z (s : ℝ) : U := if hs : s ∈ K then
    ⟨alpha ((s ^ 2 - tau) / d), hsource (hunit s hs)⟩ else
    ⟨alpha 0, hsource ⟨le_rfl, zero_le_one⟩⟩
  have hlocal (s : ℝ) (hs : s ∈ K) : (localTime s).val = tau - s ^ 2 := by
    simp only [localTime, dif_pos hs]
  have hthetaVal (s : ℝ) (hs : s ∈ K) : (theta s).val = T - s ^ 2 := by
    change (T - tau) + (localTime s).val / 1 = _
    rw [hlocal s hs]
    ring
  have hzval (s : ℝ) (hs : s ∈ K) : (z s).val = alpha ((s ^ 2 - tau) / d) := by
    simp only [z, dif_pos hs]
  have htheta : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ theta K := by
    apply M14.intervalLift_contMDiffOn 𝓘(ℝ, ℝ)
      (G.realization.timeIntervals.interval
        (cylinderPhysicalInterval (T - tau) 1 e.scale_pos J))
    exact ((contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn).congr
      (fun s hs => hthetaVal s hs)
  have hq : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => (s ^ 2 - tau) / d) :=
    (((contDiff_id.pow 2).sub contDiff_const).div_const d).contMDiff
  have hz : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 z K := by
    have hv : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun s => (z s).val) K :=
      (halpha.comp hq).contMDiffOn.congr (fun s hs => hzval s hs)
    intro s hs
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) (𝓡 3) 1) z K s).mp (hv s hs)
  let beta (s : ℝ) := rawCylinderMap G.realization e (theta s, z s)
  have hbeta : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 beta K :=
    ((rawCylinderMap_smooth G.realization e hI).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp_contMDiffOn
      ((htheta.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).prodMk hz)
  have hread (s : ℝ) : beta s = e.pointMap (localTime s).val (localTime s).property (z s).val :=
    rawCylinderMap_at_parameter G.realization e (localTime s) (z s)
  refine ⟨beta, hbeta, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (rawCylinderMap_time G.realization e (theta s, z s)).trans (hthetaVal s hs)
  · intro h0
    have hs : Real.sqrt tau ∈ K := ⟨le_rfl, horder.le⟩
    rw [hread, hzval _ hs]
    simp only [Real.sq_sqrt htau.le, sub_self, zero_div]
    have htime : localTime (Real.sqrt tau) = ⟨0, h0⟩ :=
      Subtype.ext (by rw [hlocal _ hs, Real.sq_sqrt htau.le, sub_self])
    rw [htime]
  · intro hleft
    have hs : Real.sqrt (tau + d) ∈ K := ⟨horder.le, le_rfl⟩
    rw [hread, hzval _ hs]
    rw [Real.sq_sqrt htd.le, add_sub_cancel_left, div_self hd.ne']
    have htime : localTime (Real.sqrt (tau + d)) = ⟨-d, hleft⟩ :=
      Subtype.ext (by rw [hlocal _ hs, Real.sq_sqrt htd.le]; ring)
    rw [htime]
  · intro s hs
    have hsK : s ∈ K := Ioo_subset_Icc_self hs
    have hthetaAt := ((htheta s hsK).contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
      (by simp)
    have hzAt := ((hz s hsK).contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
      (by simp)
    have henergy := rawCylinder_sourceEnergy_upper G e hI gSource 2
      (fun t ht x v => by simpa only [one_mul] using hmetric t ht x v) theta z hthetaAt hzAt
    have hzgerm : (fun r => (z r).val) =ᶠ[𝓝 s] fun r => alpha ((r ^ 2 - tau) / d) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact hzval r hr
    have hsourceEnergy : M08.referenceSpeedSq gSource (fun r => (z r).val) s ≤
        16 * rho ^ 2 * s ^ 2 / d ^ 2 := by
      unfold M08.referenceSpeedSq curveVelocity
      dsimp only
      rw [hzgerm.eq_of_nhds, hzgerm.mfderiv_eq]
      exact seed_referenceSpeedSq_bound gSource halpha hrho (hunit s hsK) hspeed
    have hscalarBound : horizontalScalarCurvature G.toLGeometry.leafwise (beta s) ≤ Q := by
      rw [hread]
      exact hscalar _ _ _
    have hscaled := mul_le_mul_of_nonneg_left hscalarBound (by positivity : 0 ≤ 2 * s ^ 2)
    change G.toLGeometry.spacetime.horizontalMetric.inner (beta s)
      (M14.projectedCurveVelocity G.toLGeometry beta s)
      (M14.projectedCurveVelocity G.toLGeometry beta s) ≤
        2 * M08.referenceSpeedSq gSource (fun r => (z r).val) s at henergy
    unfold M14.squareCurveDensity M14.projectedCurveVelocityWithin
    rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
    change 2 * s ^ 2 * horizontalScalarCurvature G.toLGeometry.leafwise (beta s) +
      (1 / 2 : ℝ) * G.toLGeometry.spacetime.horizontalMetric.inner (beta s)
        (M14.projectedCurveVelocity G.toLGeometry beta s)
        (M14.projectedCurveVelocity G.toLGeometry beta s) ≤ _
    have hbound : 2 * s ^ 2 * Q + 16 * rho ^ 2 * s ^ 2 / d ^ 2 =
        2 * s ^ 2 * (Q + 8 * rho ^ 2 / d ^ 2) := by ring
    rw [← hbound]
    linarith

end PoincareConjecture.Proofs.M46
