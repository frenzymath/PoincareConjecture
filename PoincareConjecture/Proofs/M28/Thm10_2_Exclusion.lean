import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFamilySelection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallSpatialLimit
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RetainedPositiveRecutData
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallNonnegative
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFinalChartDistanceLimit
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedMetricEndRayData
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SelectedRayScalarSequence
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SourceChartConeObstruction











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open CounterexampleNeckFamily

set_option maxHeartbeats 6400000 in





theorem exists_actual_counterexample_exclusion_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T0 : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
        ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
          (∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
            ((n : ℝ) + 1) ((n : ℝ) + 1)) → False := by
  classical
  obtain ⟨eH, heH, heHsmall, hfamily⟩ :=
    exists_counterexample_neck_family_accuracy P T0
  obtain ⟨eG, heG, _heGsmall, hgeometry⟩ :=
    exists_actual_source_criticalBall_retained_limit_accuracy P
  obtain ⟨eRecut, heRecut, _heRecutSmall, hrecut⟩ :=
    exists_retained_positive_recut_data_accuracy P
  obtain ⟨eCurv, heCurv, _heCurvSmall, hcurvature⟩ :=
    exists_source_criticalBall_nonnegative_accuracy P
  obtain ⟨eFinal, heFinal, _heFinalSmall, hfinal⟩ :=
    exists_retained_final_source_data_accuracy P
  obtain ⟨eDistance, heDistance, _heDistanceSmall, hdistance⟩ :=
    exists_source_final_chart_distance_limit_accuracy P
  obtain ⟨eScalar, heScalar, _heScalarSmall, hscalarSequence⟩ :=
    exists_selected_ray_scalar_sequence_accuracy.{0}
  obtain ⟨eRatio, heRatio, _heRatioSmall, hneckRatio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{0}
  let epsilon0 := min eH (min eG (min eRecut (min eCurv
    (min eFinal (min eDistance (min (eScalar / 2)
      (min (eRatio / 2) (neckShorteningEpsilon / 2))))))))
  have hepsilon0 : 0 < epsilon0 :=
    lt_min heH (lt_min heG (lt_min heRecut (lt_min heCurv
      (lt_min heFinal (lt_min heDistance (lt_min (by positivity)
        (lt_min (by positivity) (div_pos neckShorteningEpsilon_pos (by norm_num)))))))))
  refine ⟨epsilon0, hepsilon0, (min_le_left _ _).trans heHsmall, ?_⟩
  intro epsilon hepsilon hsmall C hC A _hA E
  have hbounds : epsilon ≤ eH ∧ epsilon ≤ eG ∧ epsilon ≤ eRecut ∧
      epsilon ≤ eCurv ∧ epsilon ≤ eFinal ∧ epsilon ≤ eDistance ∧
      epsilon ≤ eScalar / 2 ∧ epsilon ≤ eRatio / 2 ∧
      epsilon ≤ neckShorteningEpsilon / 2 := by
    simpa only [epsilon0, le_min_iff] using hsmall
  obtain ⟨hH, hG, hRecut, hCurv, hFinal, hDistance, hScalar, hRatio, hShort⟩ := hbounds
  obtain ⟨H⟩ := hfamily epsilon C A hepsilon hH hC E
  obtain ⟨W, G, _hcritical⟩ := hgeometry H hG
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  let := G.limitCarrier.secondCountable
  let D0 : LeviCivitaData G.limitMetric :=
    Classical.choice (exists_leviCivitaData G.limitMetric)
  obtain ⟨Z⟩ := hrecut H W hRecut G D0
  let T := Z.tube.tube
  let B := Z.model
  let U := Z.region
  have hfinite (p q : U) : intrinsicEDist G.limitMetric
      (U : Set G.limitCarrier.carrier) (p : G.limitCarrier.carrier)
      (q : G.limitCarrier.carrier) ≠ ⊤ := by
    have hle : intrinsicEDist G.limitMetric (U : Set G.limitCarrier.carrier)
        (p : G.limitCarrier.carrier) (q : G.limitCarrier.carrier) ≤
          intrinsicDiameter G.limitMetric (U : Set G.limitCarrier.carrier) :=
      le_sSup ⟨(p, q), rfl⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle.trans Z.diameter_bound)
  let := intrinsicOpenMetricSpace G.limitMetric U hfinite
  have hpreconnected : IsPreconnected (U : Set G.limitCarrier.carrier) := by
    rw [Z.region_tail]
    exact B.isPreconnected_tail true (by norm_num) (by norm_num)
  let : PreconnectedSpace U := Subtype.preconnectedSpace hpreconnected
  let DU : LeviCivitaData (intrinsicOpenMetric G.limitMetric U) :=
    Classical.choice (exists_leviCivitaData (intrinsicOpenMetric G.limitMetric U))
  have hsec : DU.NonnegativeSectionalCurvature :=
    (hcurvature H W hCurv G D0).2 U DU
  have hTaccuracy : T.epsilon = 2 * epsilon :=
    Z.tube.epsilon_eq.trans Z.cover_epsilon
  have hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D0.scalarCurvature y ≤ 2 * D0.scalarCurvature z := by
    intro i hi
    apply hneckRatio G.limitCarrier.carrier G.limitMetric D0 (T.chain.neck i)
    rw [T.chain.epsilon_eq i hi, hTaccuracy]
    linarith only [hRatio]
  have hshortening : T.epsilon ≤ neckShorteningEpsilon := by
    rw [hTaccuracy]
    linarith only [hShort]
  obtain ⟨S⟩ := exists_selected_end_chord_data T B U Z.region_tail
    Z.model_isotopy D0 D0.continuous_scalarCurvature.continuousOn hratio
    Z.scalar_diverges Z.diameter_pos Z.diameter_bound hshortening hfinite DU hsec
  have hfront : IsCompact (frontier (U : Set G.limitCarrier.carrier)) := by
    rw [Z.frontier_eq]
    exact B.isCompact_middleSphere
  have hcover : Z.cover.epsilon ≤ eScalar := by
    rw [Z.cover_epsilon]
    linarith only [hScalar]
  have hpositive (x : U) : 0 < D0.scalarCurvature (x : G.limitCarrier.carrier) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (Z.scalar_lower x x.property)
  obtain ⟨Pray, Qray, hdistinct, _hPheight, _hQheight⟩ :=
    exists_two_distinct_selected_metricEndRay_data T B U S.wall hfinite
      S.endPoint S.alpha S.alpha_pos S.endPoint_missing S.radius_barrier S.inward_rays
  obtain ⟨eta0, B0, rho, phi, _heta0, _hetaP, _hB0, hrho,
      _hrhoBounds, _hphi, hdata⟩ :=
    hscalarSequence G.limitCarrier.carrier G.limitMetric D0 Z.cover.X T B U
      Z.region_tail hfront Z.model_isotopy Z.cover Z.region_subset hcover hratio
      Z.scalar_diverges hpositive S.wall hfinite DU hsec S.endPoint S.alpha
      S.endPoint_missing S.alpha_pos S.tail_radius S.radius_barrier S.segments
      Pray Qray hdistinct
  let d : ℕ → ℝ := fun i => eta0 / ((phi i : ℝ) + 2)
  let x0 : ℕ → U := fun i => Pray.point (d i)
  let R : ℕ → ℝ := fun i => D0.scalarCurvature (x0 i : G.limitCarrier.carrier)
  let q : ℕ → G.limitCarrier.carrier := fun i => (x0 i : G.limitCarrier.carrier)
  let m := Real.sqrt rho
  have hm : 0 < m := Real.sqrt_pos.2 hrho
  obtain ⟨hpoint, _hd, _hcompletion, hR, _hproduct, hnormalized,
    _hclock, _hscaledRadius⟩ := hdata
  have hRpos (i : ℕ) : 0 < R i := (hpoint i).2.2.2.2.1
  have hcenter : Tendsto
      (fun i => Real.sqrt (R i) * dist (x0 i : UniformSpace.Completion U) S.endPoint)
      atTop (𝓝 m) := by
    apply hnormalized.congr'
    exact Eventually.of_forall (fun i => by
      dsimp [R, x0]
      rw [(hpoint i).2.2.1])
  obtain ⟨D⟩ := hfinal H W hFinal G D0 q Z.initial Z.initial_center
    Z.sigma Z.sigma_strictMono Z.graphs Z.graphs_smooth Z.graphs_height
    Z.graphs_image (fun i => Z.source_side (q i) (x0 i).property)
  obtain ⟨eta, heta, a, ha, ham, Fc, hoperator, hscalar, _horthonormal,
    x, hfiniteFc, hdistances, hshort⟩ :=
      hdistance H W hDistance G D0 q Z.sigma D U hfinite
        (fun i => (x0 i).property) B Z.frontier_eq hR m hm
  exact no_selected_end_source_chart_limit ricciFlowCurvatureTheory.{0}
    T B U hfinite S ha hm ham Fc hoperator hscalar
    (fun i => x0 (eta i)) (fun i => R (eta i)) (fun i => hRpos (eta i))
    (hR.comp heta.tendsto_atTop) (hcenter.comp heta.tendsto_atTop)
    x hfiniteFc (fun z w => hdistances.tendsto_at (mem_univ (z, w))) hshort

end PoincareConjecture.M28
