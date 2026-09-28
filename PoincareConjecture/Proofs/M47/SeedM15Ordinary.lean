import PoincareConjecture.Proofs.M47.JointSeedOrdinary
import PoincareConjecture.Proofs.M15.Thm8_10_ProductStable
import PoincareConjecture.Proofs.M15.Thm8_10_ProductCylinder
import PoincareConjecture.Proofs.M15.Thm8_10_StableSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M15

theorem seedM15_ordinary_volume
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    {b T tau r : ℝ} (hbt : b < T) (F : RicciFlow 3 M (Icc b T)) (x : M)
    (htau : 0 < tau) (htauAge : tau < T - b) (htauTop : tau ≤ taubar)
    (A : Set M) (hA : IsOpen A)
    (haccess : ∀ q ∈ A, reducedLength F T x q tau ≤ l0)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (T - tau)) A)
    (hr : 0 < r) (hrtau : r ^ 2 ≤ tau)
    (hcurv : ∀ s ∈ Icc (T - r ^ 2) T, ∀ q ∈ (F.metric T).ball x r,
      (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (U.kappa * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  let I : SpacetimeInterval := {
    domain := Icc b T
    ordConnected := ordConnected_Icc
    nontrivial := F.nontrivial }
  have hT : T ∈ I.domain := ⟨hbt.le, le_rfl⟩
  have hd : 0 < T - b := sub_pos.mpr hbt
  obtain ⟨P⟩ := hM12.ordinary_product M F.metric I F.smooth
  let G := ordinaryProductTransport (I := I) F P
  let t : I.domain := ⟨T, hT⟩
  let y : (G.slices T).Point := P.product.sliceIdentification t x
  have hy : G.spacetime.timeFunction y.val = T := y.property
  obtain ⟨H⟩ := hM14.conclusion (I.domain × M) (fun q => q.1.val) I G
  obtain ⟨capture⟩ := ordinaryProduct_capture (I := I) hM12 F P T (T - b) hT
  have hwindow : Icc (T - (T - b)) T ⊆ I.domain := by
    rw [sub_sub_cancel]
  have hcomplete : CompleteBoundedCurvatureOn F (Icc (T - (T - b)) T) := by
    simpa only [sub_sub_cancel] using jointSeed_completeBoundedCurvatureOn F
  obtain ⟨out, _, _, _⟩ := H.ordinary_capture hOrdinary M I P.product.productCylinder
    (ordinaryProductCylinderMetric (I := I) F P) F T (T - b) hT hd hwindow hcomplete capture
  obtain ⟨E⟩ := H.exponential.family T y.val hy
  obtain ⟨S⟩ := ordinaryProduct_exists_stableSet (I := I) F P H capture out
    htau htauAge.le y.val hy E
  have htime : T - tau ∈ I.domain := ⟨by linarith, sub_le_self _ htau.le⟩
  have hcenter : capture.point_map y.val = x := by
    change capture.point_map (P.product.sliceIdentification t x).val = x
    rw [P.product.sliceIdentification_eq]
    have h := capture.point_map_on_cylinder t x
    rwa [P.product.productCylinder_eq] at h
  obtain ⟨W, hWopen, hWS, hWlength, hWvolume⟩ := ordinaryProduct_stable_source
    (I := I) hM12 F P capture out htauAge htime hy S A hA
      (by simpa only [hcenter] using haccess) hvolume
  let K : SpacetimeInterval := {
    domain := Icc (T - r ^ 2) T
    ordConnected := ordConnected_Icc
    nontrivial := ⟨T - r ^ 2, ⟨le_rfl, sub_le_self _ (sq_nonneg r)⟩,
      T, ⟨sub_le_self _ (sq_nonneg r), le_rfl⟩,
      ne_of_lt (sub_lt_self _ (sq_pos_of_pos hr))⟩ }
  have hKI : K.domain ⊆ I.domain := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  obtain ⟨C, ⟨B⟩⟩ := ordinaryProduct_actualBallCylinder (I := I)
    hM12 hM13 F P t x hr K rfl hKI hcurv
  let : CompactSpace (G.slices T).Point :=
    (P.product.sliceIdentification t).toHomeomorph.compactSpace
  let Q : M15Theorem81Configuration G T y E taubar l0 V r K C B := {
    tau₀ := tau
    tau₀_pos := htau
    tau₀_le := htauTop
    radius_sq_le_tau₀ := hrtau
    terminal_mem := htime
    terminal_ball_compact := isClosed_closure.isCompact
    stable := S
    W := W
    W_open := hWopen
    W_subset_stable := hWS
    normalized_reduced_length := hWlength
    terminal_image_volume := hWvolume }
  have hbound := U.estimate (I.domain × M) (fun q => q.1.val) I G T y E r K C B Q
  have hcalc := ordinaryProduct_slice_calculus (I := I) hM13 F P t
  have hball : P.product.sliceIdentification t '' (F.metric T).ball x r =
      (G.slices T).metricOnPoints.ball y r := by
    simpa only [Real.sqrt_one, one_mul] using! hcalc.ball_image x r
  change ENNReal.ofReal (U.kappa * r ^ 3) ≤
    calibratedMetricVolume (G.slices T).metricOnPoints
      ((G.slices T).metricOnPoints.ball y r) at hbound
  rw [← hball] at hbound
  have hvol : calibratedMetricVolume (G.slices T).metricOnPoints
      (P.product.sliceIdentification t '' (F.metric T).ball x r) =
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
    simpa using! hcalc.volume_image ((F.metric T).ball x r)
  rwa [hvol] at hbound

end PoincareConjecture.M47
