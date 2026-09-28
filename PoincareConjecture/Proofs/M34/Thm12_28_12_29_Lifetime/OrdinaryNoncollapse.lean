import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryGeometry











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}

set_option backward.isDefEq.respectTransparency false in


theorem ordinaryChapter11_noncollapsed
    (R : OrdinaryProductRicciGeometry F.metric I)
    (C : ∀ t : I.domain,
      MetricHomothetyCalculus (F.metric t.val) (R.product.slices t.val).metricOnPoints
        (R.product.sliceIdentification t) 1)
    (p : (ordinaryChapter11Flow R).point) (kappa r0 : ℝ)
    (hvol : ∀ r : ℝ, 0 < r → r ≤ r0 → Ioc (p.1 - r ^ 2) p.1 ⊆ I.domain →
      (∀ s ∈ Ioc (p.1 - r ^ 2) p.1,
        ∀ q ∈ (F.metric p.1).ball (ordinaryChapter11Projection R p) r,
          |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (kappa * r ^ 3) ≤ calibratedMetricVolume (F.metric p.1)
        ((F.metric p.1).ball (ordinaryChapter11Projection R p) r)) :
    GeneralizedKappaNoncollapsedAt (ordinaryChapter11Flow R) p kappa r0 := by
  intro r hr hrr hI e hzero hcurv
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have hvolume := ordinarySlice_ball_volume R.product t (C t)
    (ordinaryChapter11Projection R p) r
  change calibratedMetricVolume (R.product.slices p.1).metricOnPoints
      ((R.product.slices p.1).metricOnPoints.ball
        (R.product.sliceIdentification t p.2.val.2) r) = _ at hvolume
  rw [ordinaryChapter11_identification_projection R t p.2] at hvolume
  change ENNReal.ofReal (kappa * r ^ 3) ≤
    calibratedMetricVolume (R.product.slices p.1).metricOnPoints
      ((R.product.slices p.1).metricOnPoints.ball p.2 r)
  rw [hvolume]
  apply hvol r hr hrr hI
  intro s hs q hq
  let y := R.product.sliceIdentification t q
  have hy : y ∈ ((ordinaryChapter11Flow R).metric p.1).ball p.2 r := by
    have hball := ordinarySlice_ball R.product t (C t)
      (ordinaryChapter11Projection R p) r
    change R.product.sliceIdentification t '' _ =
      (R.product.slices p.1).metricOnPoints.ball
        (R.product.sliceIdentification t p.2.val.2) r at hball
    rw [ordinaryChapter11_identification_projection R t p.2] at hball
    change y ∈ (R.product.slices p.1).metricOnPoints.ball p.2 r
    rw [← hball]
    exact ⟨q, hq, rfl⟩
  have h0 : (0 : ℝ) ∈ Ioc (-r ^ 2) 0 := ⟨neg_neg_of_pos (sq_pos_of_pos hr), le_rfl⟩
  have hsr : s - p.1 ∈ Ioc (-r ^ 2) 0 := by
    constructor <;> linarith [hs.1, hs.2]
  have h := hcurv (s - p.1) hsr y hy
  rw [ordinaryChapter11_curvatureNorm_eq R C] at h
  rw [ordinaryChapter11Projection_cylinder_based R p e isPreconnected_Ioc
    h0 (hzero h0) hy hsr] at h
  change |(F.connection (p.1 + (s - p.1) / 1)).curvatureTensorNorm y.val.2| ≤ _ at h
  have hclock : p.1 + (s - p.1) / 1 = s := by ring
  have hspatial : y.val.2 = q := congrArg Prod.snd (R.product.sliceIdentification_eq t q)
  rwa [hclock, hspatial] at h

end PoincareConjecture.M34
