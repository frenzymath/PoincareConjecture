import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryConfiguration
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryBallCylinder
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryPositiveSurvival
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.PartialFlowCapture
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.LateReducedLengthVolume
import PoincareConjecture.Proofs.M34.Standard.ClosedCylinderCurvature

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in

theorem partialFlow_late_small_ball_volume {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ t ∈ Ico (F.lifetime / 2) F.lifetime,
      ∀ p : StandardCapSpace, ∀ r : ℝ, 0 < r → r ≤ Real.sqrt (F.lifetime / 8) →
        (∀ s ∈ Ioc (t - r ^ 2) t, ∀ q ∈ (F.flow.metric t).ball p r,
          |(F.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (kappa * r ^ 3) ≤
          calibratedMetricVolume (F.flow.metric t) ((F.flow.metric t).ball p r) := by
  obtain ⟨l0, V, hl0, hV, hregion⟩ := partialFlow_fixed_early_reduced_length_volume F P.curvature
  obtain ⟨U15⟩ := P.noncollapse_generalized F.lifetime l0 V F.lifetime_pos hl0 hV
  obtain ⟨R, hRicci⟩ := partialFlow_ordinary_product F P
  let I := partialFlowSpacetimeInterval F
  let G := ordinaryProductLGeometry R hRicci
  obtain ⟨Cexp⟩ := P.exponential (I.domain × StandardCapSpace) (fun z => z.1.val) I G
  refine ⟨U15.kappa, U15.kappa_pos, ?_⟩
  intro t ht p r hr hr0 hcurv
  have ht0 : t ∈ Ioo 0 F.lifetime := ⟨by linarith [ht.1, F.lifetime_pos], ht.2⟩
  have hT : t ∈ I.domain := ⟨ht0.1.le, ht.2⟩
  have hsigma : 0 < F.lifetime / 8 := by linarith [F.lifetime_pos]
  have htau : 0 < t - F.lifetime / 8 := by linarith [ht.1, F.lifetime_pos]
  have hmax : t - F.lifetime / 8 < t := by linarith
  have hclock : t - (t - F.lifetime / 8) = F.lifetime / 8 := by ring
  have hmem : t - (t - F.lifetime / 8) ∈ I.domain := by
    rw [hclock]
    exact ⟨hsigma.le, by linarith [F.lifetime_pos]⟩
  have hrsq : r ^ 2 ≤ F.lifetime / 8 := by
    calc
      r ^ 2 ≤ (Real.sqrt (F.lifetime / 8)) ^ 2 :=
        (sq_le_sq₀ hr.le (Real.sqrt_nonneg _)).mpr hr0
      _ = _ := Real.sq_sqrt hsigma.le
  have hI : Icc (t - r ^ 2) t ⊆ I.domain := by
    intro s hs
    exact ⟨by linarith [hs.1, ht.1, F.lifetime_pos], hs.2.trans_lt ht.2⟩
  obtain ⟨out⟩ := partialFlow_ordinary_capture F P R hRicci ht0
  obtain ⟨Omega, hOmega, hvolume, hlength⟩ := hregion t ht out.L out.Dlength out.V p
  have hex := ordinaryProduct_stableSet (I := I) (F := F.flow) R hRicci Cexp
    out.L hT htau hmax.le p
  have hbase : R.product.productCylinder.toSpacetime (⟨t, hT⟩, p) =
      (R.product.sliceIdentification ⟨t, hT⟩ p).val := by
    rw [R.product.productCylinder_eq, R.product.sliceIdentification_eq]
  rw [hbase] at hex
  obtain ⟨E, ⟨H⟩⟩ := hex
  have C := P.metric_homothety StandardCapSpace (R.product.slices t).Point
    (F.flow.metric t) (R.product.slices t).metricOnPoints
    (R.product.sliceIdentification ⟨t, hT⟩) 1 zero_lt_one
    (ordinarySlice_metricHomothety R.product ⟨t, hT⟩)
  have hclosed := closed_cylinder_curvature_bound F.flow
    (show t - r ^ 2 < t by nlinarith [sq_pos_of_pos hr]) hI
    ((F.flow.metric t).ball p r) hcurv
  obtain ⟨B⟩ := ordinaryProduct_ballCylinder (I := I) (F := F.flow)
    R hRicci hT p hr C hI hclosed
  obtain ⟨configuration⟩ := ordinaryProduct_configuration (I := I) (F := F.flow)
    R hRicci hT p out E H C (partialFlow_complete F P.curvature hT)
    hmax (show t - F.lifetime / 8 ≤ F.lifetime by linarith [ht.2])
    (show r ^ 2 ≤ t - F.lifetime / 8 by linarith [ht.1, F.lifetime_pos])
    hmem hOmega (by simpa only [hclock] using hvolume) hlength B
  have hbound := U15.estimate (I.domain × StandardCapSpace) (fun z => z.1.val) I G t
    (R.product.sliceIdentification ⟨t, hT⟩ p) E r (ordinaryBallInterval t r hr)
    (ordinaryBallSource (F.flow.metric t) p r) B configuration
  change ENNReal.ofReal (U15.kappa * r ^ 3) ≤
    calibratedMetricVolume (R.product.slices t).metricOnPoints
      ((R.product.slices t).metricOnPoints.ball (R.product.sliceIdentification ⟨t, hT⟩ p) r)
    at hbound
  rwa [ordinarySlice_ball_volume R.product ⟨t, hT⟩ C] at hbound

end PoincareConjecture.M34
