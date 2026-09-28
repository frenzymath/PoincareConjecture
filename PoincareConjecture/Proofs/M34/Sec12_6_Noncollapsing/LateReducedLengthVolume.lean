import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.LateConnectorBounds

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal intervalIntegral

namespace PoincareConjecture.M34

theorem partialFlow_fixed_early_reduced_length_volume {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : RicciFlowCurvatureTheory.{0}) :
    ∃ l0 V : ℝ, 0 < l0 ∧ 0 < V ∧ ∀ t ∈ Ico (F.lifetime / 2) F.lifetime,
      ∀ _L : LGeodesicTheory F.flow t t,
      ∀ _D : ReducedLengthDifferentialTheory F.flow t t,
      ∀ _RV : ReducedVolumeTheory F.flow t t, ∀ p : StandardCapSpace,
        ∃ Omega : Set StandardCapSpace, IsOpen Omega ∧
          ENNReal.ofReal V ≤ calibratedMetricVolume (F.flow.metric (F.lifetime / 8)) Omega ∧
          ∀ y ∈ Omega, reducedLength F.flow t p y (t - F.lifetime / 8) ≤ l0 := by
  have hL := F.lifetime_pos
  have hslab : F.lifetime / 2 ∈ Ico 0 F.lifetime := by
    constructor <;> linarith [F.lifetime_pos]
  obtain ⟨delta, d, V, hdelta, hd, hV, hcharts⟩ :=
    partialFlow_early_coordinate_packet F P hslab
  obtain ⟨K, hK, hcurv⟩ := F.curvature_locally_bounded _ hslab.1 hslab.2
  obtain ⟨C, hC, htransition⟩ := Real.smoothTransition.exists_deriv_bound
  let speed := d * (C / ((F.lifetime / 8) / (2 * Real.sqrt F.lifetime))) * delta
  let A := 2 * F.lifetime * (9 * K) + speed ^ 2 / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let N := (3 + A) * Real.sqrt F.lifetime
  have hN : 0 ≤ N := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  let l0 := 1 + N / (2 * Real.sqrt (F.lifetime / 8))
  have hl0 : 0 < l0 := by dsimp [l0]; positivity
  refine ⟨l0, V, hl0, hV, ?_⟩
  intro t ht L D RV p
  have h1 : 0 < t - F.lifetime / 4 := by linarith [ht.1, F.lifetime_pos]
  have h0 : 0 < t - F.lifetime / 8 := by linarith [ht.1, F.lifetime_pos]
  have h10 : t - F.lifetime / 4 < t - F.lifetime / 8 := by linarith [F.lifetime_pos]
  have h1max : t - F.lifetime / 4 < t := by linarith [F.lifetime_pos]
  have h0max : t - F.lifetime / 8 < t := by linarith [F.lifetime_pos]
  obtain ⟨q, _, hq⟩ := RV.minimum_bound p _ h1 h1max
  obtain ⟨f, hf0, hsource, hpacket⟩ := hcharts q
  let Omega := f '' Metric.ball 0 delta
  have hOmega : IsOpen Omega :=
    f.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hsource
  have hsigma : F.lifetime / 8 ∈ Icc 0 (F.lifetime / 2) := by
    constructor <;> linarith [F.lifetime_pos]
  refine ⟨Omega, hOmega, (hpacket _ hsigma).2, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 delta) :=
    f.contMDiffOn_toFun.mono hsource
  let beta := coordinateConnector f (Real.sqrt (t - F.lifetime / 4))
    (Real.sqrt (t - F.lifetime / 8)) z
  have hend := coordinateConnector_endpoints f (Real.sqrt_lt_sqrt h1.le h10) z
  have hstart : beta (Real.sqrt (t - F.lifetime / 4)) = q := hend.1.trans hf0
  have hact : (∫ s in Real.sqrt (t - F.lifetime / 4)..Real.sqrt (t - F.lifetime / 8),
      Proofs.M09.squareCurveActionDensity F.flow t beta s) ≤ A * Real.sqrt F.lifetime :=
    late_coordinate_connector_action_le F P hdelta hd hC hK htransition hcurv f hf
      (fun u hu => (hpacket u hu).1) ht hz
  obtain ⟨E⟩ := D.exponential_geometry p
  have hwindow : Icc (t - t) t ⊆ Ico 0 F.lifetime := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
  have hred := reducedLength_le_of_smooth_connector F.flow P t t
    (by linarith [ht.1, F.lifetime_pos]) hwindow L h1 h10 h0max p q (f z)
    E hq beta (coordinateConnector_contMDiff f _ _ hz hf) hstart hend.2 hact
  have hsqrt1 : Real.sqrt (t - F.lifetime / 4) ≤ Real.sqrt F.lifetime :=
    Real.sqrt_le_sqrt (by linarith [ht.2, F.lifetime_pos])
  have hsqrt0 : Real.sqrt (F.lifetime / 8) ≤ Real.sqrt (t - F.lifetime / 8) :=
    Real.sqrt_le_sqrt (by linarith [ht.1, F.lifetime_pos])
  have hnum : (3 : ℝ) * Real.sqrt (t - F.lifetime / 4) + A * Real.sqrt F.lifetime ≤ N := by
    dsimp [N]
    nlinarith
  calc
    reducedLength F.flow t p (f z) (t - F.lifetime / 8) ≤
        N / (2 * Real.sqrt (t - F.lifetime / 8)) :=
      hred.trans (div_le_div_of_nonneg_right hnum (by positivity))
    _ ≤ N / (2 * Real.sqrt (F.lifetime / 8)) :=
      div_le_div_of_nonneg_left hN
        (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by linarith [F.lifetime_pos])))
        (mul_le_mul_of_nonneg_left hsqrt0 (by norm_num))
    _ ≤ l0 := by dsimp [l0]; linarith

end PoincareConjecture.M34
