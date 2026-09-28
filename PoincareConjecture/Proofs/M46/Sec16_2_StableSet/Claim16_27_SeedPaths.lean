import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedLift
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedComparison
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SpatialPath
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_RealizedSeed
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_OldSeedVolume











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : SurgeryFlowData.{u}} {window : M33RegularHistoryWindow F}



theorem history_point_eq_of_physical_heq (R : M46RegularSpacetimeData window)
    {s t : ℝ} (hs : s ∈ R.history.generalized.interval)
    (ht : t ∈ R.history.generalized.interval)
    (z : (R.history.generalized.slice s).carrier)
    (w : (R.history.generalized.slice t).carrier) (hst : s = t)
    (himage : HEq (R.history.history.forward s hs z) (R.history.history.forward t ht w)) :
    (⟨s, z⟩ : R.history.generalized.point) = ⟨t, w⟩ := by
  subst t
  have hz := (R.history.history.forward_openEmbedding s hs).injective (eq_of_heq himage)
  rw [hz]



theorem realized_seed_point_eq (R : M46RegularSpacetimeData window)
    {t : ℝ} (ht : t ∈ R.history.generalized.interval)
    (q : (R.geometry.toLGeometry.slices t).Point)
    (z : (R.history.generalized.slice t).carrier)
    (himage : R.history.history.forward t ht z = R.history.history.forward t ht
      ((R.geometry.sliceIdentification t).identification.symm q)) :
    (⟨t, z⟩ : R.geometry.toLGeometry.Point) = q.val := by
  have hz := (R.history.history.forward_openEmbedding t ht).injective himage
  rw [hz]
  have hpoint :
      ((R.geometry.sliceIdentification t).identification
        ((R.geometry.sliceIdentification t).identification.symm q)).val =
      (⟨t, (R.geometry.sliceIdentification t).identification.symm q⟩ :
        R.geometry.toLGeometry.Point) :=
    (R.geometry.sliceIdentification t).identification_eq _
  exact hpoint.symm.trans (congrArg Subtype.val
    ((R.geometry.sliceIdentification t).identification.apply_symm_apply q))



theorem seed_image_comparisons
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {O : SurgeryObservation F} (old : SurgeryPrefixControls p F O)
    (hpinch : SurgeryFlowPinched F) (R : M46RegularSpacetimeData window)
    {B T S tau : ℝ} (hB : 1 ≤ B) {x endpoint : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S x endpoint)
    (hmin : M14IsMinimizing path) (htau : 0 < tau) (htauS : tau ≤ S)
    (hS : S ≤ surgeryEpochStart (p.i + 1))
    (htotal : tau + seedImageDelay B (p.r (Fin.last p.i)) ≤ surgeryEpochStart (p.i + 1))
    (hfloor : ∀ s ∈ Icc 0 S,
      -6 ≤ horizontalScalarCurvature R.geometry.toLGeometry.leafwise (path.curve s))
    (hshort : M14BackwardLAction R.geometry.toLGeometry path ≤ 3 * Real.sqrt S)
    (htold : T - tau ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (htime : ∀ s ∈ Icc (-seedImageDelay B (p.r (Fin.last p.i))) 0,
      (T - tau) + s / 1 ∈ R.history.generalized.interval)
    (htime0 : T - tau ∈ R.history.generalized.interval)
    (y0 : (R.history.generalized.slice (T - tau)).carrier)
    (x0 : (F.slice (T - tau)).carrier)
    (hx0 : R.history.history.forward (T - tau) htime0 y0 = x0)
    (hpoint : path.curve tau = (⟨T - tau, y0⟩ : R.geometry.toLGeometry.Point))
    (hpositive : ¬ SurgeryPositiveComponentAt F (T - tau) x0)
    (e : SurgeryFlowCylinder F (F.slice (T - tau)) (T - tau) 1
      (Icc (-seedCylinderDuration B (p.r (Fin.last p.i))) 0)
      ((F.metric (T - tau)).ball x0 (p.r (Fin.last p.i) / (8 * B))))
    (hbase : ∀ h y, y ∈ (F.metric (T - tau)).ball x0 (p.r (Fin.last p.i) / (8 * B)) →
      HEq (e.forward 0 h y) y)
    (hscalar : ∀ s hs y,
      y ∈ (F.metric (T - tau)).ball x0 (p.r (Fin.last p.i) / (8 * B)) →
      (F.connection ((T - tau) + s / 1)).scalarCurvature (e.forward s hs y) ≤
        4 * (p.r (Fin.last p.i))⁻¹ ^ 2)
    (hRm : ∀ s hs y,
      y ∈ (F.metric (T - tau)).ball x0 (p.r (Fin.last p.i) / (8 * B)) →
      (F.connection ((T - tau) + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤
        52 * (p.r (Fin.last p.i))⁻¹ ^ 2) :
    ∃ A : Set (R.geometry.toLGeometry.slices
        (T - (tau + seedImageDelay B (p.r (Fin.last p.i))))).Point,
      IsOpen A ∧ A.Nonempty ∧
      ENNReal.ofReal (p.kappa (Fin.last p.i) *
        seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8) ≤
        calibratedMetricVolume (R.geometry.toLGeometry.slices
          (T - (tau + seedImageDelay B (p.r (Fin.last p.i))))).metricOnPoints A ∧
      ∀ q ∈ closure A, ∃ comparison : M14BackwardPath R.geometry.toLGeometry T 0
          (tau + seedImageDelay B (p.r (Fin.last p.i))) x q.val,
        M14BackwardLAction R.geometry.toLGeometry comparison < actionBudget p / 2 := by
  let r := p.r (Fin.last p.i)
  let d := seedImageDelay B r
  let rho := seedImageRadius B r
  let duration := seedCylinderDuration B r
  let U : TopologicalSpace.Opens (F.slice (T - tau)).carrier :=
    ⟨(F.metric (T - tau)).ball x0 (r / (8 * B)), M04.initial_ball_isOpen _ _ _⟩
  have hr : 0 < r := p.r_pos _
  have hd : 0 < d := seedImageDelay_pos hB hr
  have hrho : 0 < rho := seedImageRadius_pos hB hr
  have hduration : d < duration := seedImageDelay_lt_duration hB hr
  let J : SpacetimeInterval := ⟨Icc (-d) 0, ordConnected_Icc,
    ⟨-d, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩⟩
  have hJ : J.domain = Icc (-d) 0 := rfl
  have hzero : 0 ∈ J.domain := ⟨by linarith, le_rfl⟩
  have hleft : -d ∈ J.domain := ⟨le_rfl, by linarith⟩
  have hsub : J.domain ⊆ Icc (-duration) 0 := Icc_subset_Icc_left (by linarith)
  obtain ⟨lifted, hforward, hpullback⟩ :=
    exists_realized_seed_cylinder R hd hduration hJ (U := U) e htime
  have hI : (cylinderPhysicalInterval (T - tau) 1 lifted.scale_pos J).domain ⊆
      R.history.generalized.interval := by
    rintro _ ⟨s, hs, rfl⟩
    exact htime s hs
  have hmetric (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val) :
      lifted.pullbackInner s hs z.val v v ≤ 2 * (F.metric (T - tau)).inner z.val v v := by
    rw [hpullback s hs z.val z.property v v]
    have hsmall : 6 * (52 * r⁻¹ ^ 2) * (-s) ≤ 1 / 2 := by
      apply le_trans _ (seedImageDelay_metric_short hB hr)
      exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) (by positivity)
    simpa only [SurgeryFlowCylinder.pullbackInner, one_mul] using
      (based_cylinder_metric_comparison_two P44 hpinch e U.isOpen hbase z.property v
        (hsub hs) hsmall (fun t ht => hRm t ht z.val z.property)).2
  have hscalarLift (s : ℝ) (hs : s ∈ J.domain) (z : U) :
      horizontalScalarCurvature R.geometry.toLGeometry.leafwise
        (lifted.pointMap s hs z.val) ≤ 4 * r⁻¹ ^ 2 := by
    rw [realized_seed_cylinder_scalar P R lifted s hs (htime s hs) z,
      hforward s hs z.val z.property]
    exact hscalar s (hsub hs) z.val z.property
  obtain ⟨hleftFull, hAopen, hAcompact, hAregular, hAvolume⟩ :=
    old_seed_image_volume P44 p old hpinch htold x0 hpositive hB e hbase hRm
  let Aphysical := e.forward (-d) hleftFull '' (F.metric (T - tau)).ball x0 rho
  obtain ⟨A, hA, _, _, hclosure, hvolume⟩ :=
    realized_seed_of_regular_image P R (htime (-d) hleft) hAopen hAcompact hAregular
  have hvolumeA : ENNReal.ofReal (p.kappa (Fin.last p.i) * rho ^ 3 / 8) ≤
      calibratedMetricVolume (R.geometry.toLGeometry.slices ((T - tau) + -d / 1)).metricOnPoints
        A := by
    rw [hvolume]
    exact hAvolume
  have hne : A.Nonempty := by
    by_contra hn
    have hempty : A = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [hempty, measure_empty] at hvolumeA
    have hkappa := p.kappa_pos (Fin.last p.i)
    have hpos : 0 < ENNReal.ofReal (p.kappa (Fin.last p.i) * rho ^ 3 / 8) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact (not_le_of_gt hpos) hvolumeA
  have hbuffer : closure ((F.metric (T - tau)).ball x0 rho) ⊆ U := by
    have hhalf := M04.initial_half_ball_closure_subset_initial_ball (F.metric (T - tau)) x0
      (by positivity : 0 < 2 * rho)
    rw [show 2 * rho / 2 = rho by ring] at hhalf
    intro z hz
    exact (hhalf hz).trans_le
      (ENNReal.ofReal_le_ofReal (twice_seedImageRadius_lt_ball_radius hB hr).le)
  have hsourceCompact : IsCompact (closure ((F.metric (T - tau)).ball x0 rho)) :=
    (F.slices_compact (T - tau) (O.interval_subset htold.1)).of_isClosed_subset
      isClosed_closure (subset_univ _)
  let chart := M44.cylinderSliceChart e U.isOpen (-d) hleftFull
  have hphysicalClosure := chart.toOpenPartialHomeomorph.image_closure_of_compact_buffer
    hsourceCompact hbuffer
  change e.forward (-d) hleftFull '' closure ((F.metric (T - tau)).ball x0 rho) =
    closure Aphysical at hphysicalClosure
  have htEq : T - (tau + d) = (T - tau) + -d / 1 := by ring
  change ∃ A : Set (R.geometry.toLGeometry.slices (T - (tau + d))).Point, _
  rw [htEq]
  refine ⟨A, hA, hne, hvolumeA, ?_⟩
  intro q hq
  have hqImage := mem_image_of_mem
    (R.history.history.forward ((T - tau) + -d / 1) (htime (-d) hleft) ∘
      (R.geometry.sliceIdentification ((T - tau) + -d / 1)).identification.symm) hq
  rw [hclosure, ← hphysicalClosure] at hqImage
  obtain ⟨z, hz, hzImage⟩ := hqImage
  obtain ⟨alpha, halpha0, halpha1, halpha, halphaSource, halphaSpeed⟩ :=
    exists_seed_spatial_path (F.metric (T - tau)) x0 hrho hz
  have hsource : MapsTo alpha (Icc (0 : ℝ) 1) U := by
    intro s hs
    exact (halphaSource hs).trans_le
      (ENNReal.ofReal_le_ofReal (twice_seedImageRadius_lt_ball_radius hB hr).le)
  obtain ⟨beta, hbeta, hbetaClock, hbeta0, hbeta1, hbetaDensity⟩ :=
    exists_seed_cylinder_tail R.geometry htau hd hrho.le hJ lifted hI
      (F.metric (T - tau)) hmetric hscalarLift alpha halpha hsource halphaSpeed
  have hx0U : x0 ∈ U := halpha0 ▸ hsource ⟨le_rfl, zero_le_one⟩
  have hjoin : beta (Real.sqrt tau) = path.curve tau := by
    rw [hbeta0 hzero, halpha0, hpoint]
    have himage0 := hforward 0 hzero x0 hx0U
    have hphysical0 : HEq
        (R.history.history.forward ((T - tau) + 0 / 1) (htime 0 hzero)
          (lifted.forward 0 hzero x0)) x0 :=
      himage0.heq.trans (hbase (hsub hzero) x0 hx0U)
    change (⟨(T - tau) + 0 / 1, lifted.forward 0 hzero x0⟩ :
      R.history.generalized.point) = ⟨T - tau, y0⟩
    exact history_point_eq_of_physical_heq R (htime 0 hzero) htime0
      (lifted.forward 0 hzero x0) y0 (by ring) (hphysical0.trans hx0.symm.heq)
  have hend : beta (Real.sqrt (tau + d)) = q.val := by
    rw [hbeta1 hleft, halpha1]
    apply realized_seed_point_eq R (htime (-d) hleft) q
    exact (hforward (-d) hleft z (hbuffer hz)).trans hzImage
  obtain ⟨LG⟩ := P.m14.conclusion _ _ _ R.geometry.toLGeometry
  have hcomparison := admissible_seed_comparison_of_square_tail P.m12 LG p hB path hmin
    htau htauS hS htotal hfloor hshort beta hbeta hbetaClock hjoin hbetaDensity
  rw [hend] at hcomparison
  exact hcomparison

end PoincareConjecture.Proofs.M46
