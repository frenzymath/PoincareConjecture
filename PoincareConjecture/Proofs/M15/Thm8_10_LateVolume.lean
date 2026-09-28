import PoincareConjecture.Proofs.M15.Thm8_1_Assembly
import PoincareConjecture.Proofs.M15.Thm8_10_LateReducedLength
import PoincareConjecture.Proofs.M15.Thm8_10_InitialBallMeasure
import PoincareConjecture.Proofs.M15.Thm8_10_Components
import PoincareConjecture.Proofs.M15.Thm8_10_ProductStable
import PoincareConjecture.Proofs.M15.Thm8_10_ProductCylinder
import PoincareConjecture.Proofs.M15.Thm8_10_StableSource

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_compact_late_volume_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3)
    (omega T0 : ℝ) (homega : 0 < omega) (hT0 : 0 < T0) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
        [CompactSpace M] [ConnectedSpace M]
        (T : ℝ) (F : RicciFlow 3 M (Icc 0 T))
        (D : M15CompactTheorem810Data M T F omega T0),
        1 / (32 * (3 : ℝ) ^ 6) ≤ D.t₀ →
        M15CompactTheorem810Estimate D kappa := by
  obtain ⟨l0, hl0, hlength⟩ := exists_compact_late_reducedLength_bound hM04
  obtain ⟨V, hV, hvolume⟩ := exists_compact_initial_ball_volume_bound 3 (by decide) omega homega
  obtain ⟨U⟩ := generalizedUniformTheorem hM04 3 hM12 hM13 hM14 T0 l0 V hT0 hl0 hV
  refine ⟨U.kappa / 8, div_pos U.kappa_pos (by norm_num), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ T F D hlate
  let delta : ℝ := 1 / (32 * (3 : ℝ) ^ 6)
  have hdelta : 0 < delta := by norm_num [delta]
  change delta ≤ D.t₀ at hlate
  have ht0 : 0 < D.t₀ := hdelta.trans_le hlate
  let I : SpacetimeInterval := {
    domain := Icc 0 T
    ordConnected := F.interval
    nontrivial := F.nontrivial
  }
  obtain ⟨P⟩ := hM12.ordinary_product M F.metric I F.smooth
  let G := ordinaryProductTransport (I := I) F P
  let t : I.domain := ⟨D.t₀, D.t₀_mem⟩
  let x : (G.slices D.t₀).Point := P.product.sliceIdentification t D.p
  have hx : G.spacetime.timeFunction x.val = D.t₀ := x.property
  obtain ⟨H⟩ := hM14.conclusion (I.domain × M) (fun q => q.1.val) I G
  obtain ⟨capture⟩ := ordinaryProduct_capture (I := I) hM12 F P D.t₀ D.t₀ D.t₀_mem
  have hwindow : Icc (D.t₀ - D.t₀) D.t₀ ⊆ I.domain := by
    intro s hs
    exact ⟨by simpa only [sub_self] using hs.1, hs.2.trans D.t₀_le_T⟩
  have hcomplete := compact_completeBoundedCurvatureOn F isCompact_Icc hwindow
  obtain ⟨out, _, _, _⟩ := H.ordinary_capture hOrdinary M I P.product.productCylinder
    (ordinaryProductCylinderMetric (I := I) F P) F D.t₀ D.t₀ D.t₀_mem ht0 hwindow hcomplete capture
  obtain ⟨E⟩ := H.exponential.family D.t₀ x.val hx
  let b := D.t₀ - delta / 4
  have hb : 0 < b := sub_pos.mpr ((div_lt_self hdelta (by norm_num : (1 : ℝ) < 4)).trans_le hlate)
  have hbt : b < D.t₀ := by dsimp only [b]; linarith
  have hphysical : D.t₀ - b = delta / 4 := by dsimp only [b]; ring
  have hearly : delta / 4 ∈ Icc 0 (min T delta) := by
    refine ⟨by positivity, le_min ?_ ?_⟩
    · exact (by linarith : delta / 4 ≤ D.t₀).trans D.t₀_le_T
    · linarith
  have htime : D.t₀ - b ∈ I.domain := by
    rw [hphysical]
    exact ⟨hearly.1, hearly.2.trans (min_le_left _ _)⟩
  obtain ⟨S⟩ := ordinaryProduct_exists_stableSet (I := I) F P H capture out hb hbt.le x.val hx E
  have hinit (q : M) : (F.connection 0).curvatureTensorNorm q ≤ 1 :=
    (le_abs_self _).trans (D.initial_curvature_bound q)
  obtain ⟨q0, hq0⟩ := hlength M T D.T_pos F hinit D.t₀ D.t₀_le_T hlate
    (capture.point_map x.val) out.L out.V
  have hballvolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (F.metric (D.t₀ - b)) ((F.metric 0).ball q0 1) := by
    rw [hphysical]
    exact hvolume M T D.T_pos F hinit D.initial_unit_ball_volume
      (delta / 4) hearly q0
  obtain ⟨W, hWopen, hWS, hWlength, hWvolume⟩ := ordinaryProduct_stable_source
    (I := I) hM12 F P capture out hbt htime hx S ((F.metric 0).ball q0 1)
      (M04.initial_ball_isOpen (F.metric 0) q0 1) hq0 hballvolume
  let r := D.r / 2
  have hr : 0 < r := half_pos D.radius_pos
  have hrle : r ≤ D.r := half_le_self D.radius_pos.le
  have hr2 : r ^ 2 ≤ D.r ^ 2 := (sq_le_sq₀ hr.le D.radius_pos.le).mpr hrle
  have hrb : r ^ 2 ≤ b := by
    calc
      r ^ 2 = D.r ^ 2 / 4 := by dsimp only [r]; ring
      _ ≤ D.t₀ / 4 := div_le_div_of_nonneg_right D.radius_sq_le_t₀ (by norm_num)
      _ ≤ D.t₀ - D.t₀ / 4 := by linarith only [ht0]
      _ ≤ b := sub_le_sub_left (div_le_div_of_nonneg_right hlate (by norm_num)) _
  let K : SpacetimeInterval := {
    domain := Icc (D.t₀ - r ^ 2) D.t₀
    ordConnected := ordConnected_Icc
    nontrivial := ⟨D.t₀ - r ^ 2,
      ⟨le_rfl, sub_le_self _ (sq_nonneg r)⟩,
      D.t₀, ⟨sub_le_self _ (sq_nonneg r), le_rfl⟩,
      ne_of_lt (sub_lt_self _ (sq_pos_of_pos hr))⟩
  }
  have hKI : K.domain ⊆ I.domain := by
    intro s hs
    change s ∈ Icc (D.t₀ - r ^ 2) D.t₀ at hs
    exact D.time_window ⟨by linarith [hs.1], hs.2⟩
  have hballs : (F.metric D.t₀).ball D.p r ⊆ (F.metric D.t₀).ball D.p D.r := by
    intro q hq
    exact hq.trans_le (ENNReal.ofReal_le_ofReal hrle)
  have hcurv : ∀ s ∈ K.domain, ∀ q ∈ (F.metric t.val).ball D.p r,
      (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2 := by
    intro s hs q hq
    change s ∈ Icc (D.t₀ - r ^ 2) D.t₀ at hs
    have hs' : s ∈ Icc (D.t₀ - D.r ^ 2) D.t₀ :=
      ⟨by linarith [hs.1], hs.2⟩
    apply (le_abs_self _).trans ((D.curvature_bound s hs' q (hballs hq)).trans ?_)
    exact (sq_le_sq₀ (inv_nonneg.mpr D.radius_pos.le) (inv_nonneg.mpr hr.le)).mpr
      ((inv_le_inv₀ D.radius_pos hr).mpr hrle)
  obtain ⟨C, ⟨B⟩⟩ :=
    ordinaryProduct_actualBallCylinder (I := I) hM12 hM13 F P t D.p hr K rfl hKI hcurv
  let : CompactSpace (G.slices D.t₀).Point :=
    (P.product.sliceIdentification t).toHomeomorph.compactSpace
  let configuration : M15Theorem81Configuration G D.t₀ x E T0 l0 V r K C B := {
    tau₀ := b
    tau₀_pos := hb
    tau₀_le := hbt.le.trans (D.t₀_le_T.trans D.T_le_T₀)
    radius_sq_le_tau₀ := hrb
    terminal_mem := htime
    terminal_ball_compact := isClosed_closure.isCompact
    stable := S
    W := W
    W_open := hWopen
    W_subset_stable := hWS
    normalized_reduced_length := hWlength
    terminal_image_volume := hWvolume
  }
  have hbound := U.estimate (I.domain × M) (fun q => q.1.val) I G D.t₀ x E r K C B configuration
  have hcalc := ordinaryProduct_slice_calculus (I := I) hM13 F P t
  have hball : P.product.sliceIdentification t '' (F.metric D.t₀).ball D.p r =
      (G.slices D.t₀).metricOnPoints.ball x r := by
    simpa only [Real.sqrt_one, one_mul] using! hcalc.ball_image D.p r
  have hvol : calibratedMetricVolume (G.slices D.t₀).metricOnPoints
      ((G.slices D.t₀).metricOnPoints.ball x r) =
        calibratedMetricVolume (F.metric D.t₀) ((F.metric D.t₀).ball D.p r) := by
    rw [← hball]
    simpa using!
      hcalc.volume_image ((F.metric D.t₀).ball D.p r)
  change ENNReal.ofReal (U.kappa * r ^ 3) ≤
    calibratedMetricVolume (G.slices D.t₀).metricOnPoints
      ((G.slices D.t₀).metricOnPoints.ball x r) at hbound
  rw [hvol] at hbound
  change ENNReal.ofReal (U.kappa / 8 * D.r ^ 3) ≤ _
  have hscale : U.kappa / 8 * D.r ^ 3 = U.kappa * r ^ 3 := by dsimp only [r]; ring
  rw [hscale]
  exact hbound.trans (measure_mono hballs)

end PoincareConjecture.Proofs.M15
