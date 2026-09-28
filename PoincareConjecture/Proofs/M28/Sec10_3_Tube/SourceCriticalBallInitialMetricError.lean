import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialGeometry
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialCoefficients
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawChartBounds
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CapturedCylinderErrors











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube PoincareConjecture.Proofs.M28.NeckTransfer PoincareConjecture.Proofs.M28.FiniteHessian

set_option maxHeartbeats 2400000 in




theorem exists_retained_initial_metric_error_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∀ (W : CriticalBallSourcePacket H)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ n : ℕ, n + 1 ≤ ⌊epsilon⁻¹⌋₊ → ∀ rho : ℝ, 0 < rho →
            ∃ K : ℕ, ∀ k ≥ K, ∀ z : RoundCylinderSpace,
              z.2 ∈ Ioo (-(3 * epsilon / 2)⁻¹) (3 * epsilon / 2)⁻¹ → ∀ r ≤ n + 1,
                ‖iteratedFDeriv ℝ r (fun x => G.limitMetric.pullbackCoefficients
                    (capturedCylinderMap
                      (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                        W.high_index G k)
                      ((W.tube (W.high_index (G.subsequence k))).list.node 0).2 z.1 z.2) x -
                  (H.normalizedSliceMetric (W.high_index (G.subsequence k))).pullbackCoefficients
                    (cylinderNeckChart
                      ((W.tube (W.high_index (G.subsequence k))).list.node 0).2 z.1 z.2) x) 0‖ ≤
                  rho := by
  classical
  obtain ⟨epsilon₀, hpos, hsmall, hcapture⟩ := exists_retained_initial_node_capture_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro n hn
  obtain ⟨j, hj⟩ := hcapture H hepsilon W G
  let idx := fun k => W.high_index (G.subsequence k)
  let N := fun k => ((W.tube (idx k)).list.node 0).2
  let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos W.high_index G
  let eta := 3 * epsilon / 2
  have hepsN (k : ℕ) : (N k).epsilon = epsilon :=
    (W.tube (idx k)).initial_node_geometry.1
  have hepspos : 0 < epsilon := hepsN 0 ▸ (N 0).epsilon_pos
  have hepseta : epsilon ≤ eta := by dsimp only [eta]; linarith
  have hetahalf : eta < 1 / 2 := by dsimp only [eta]; linarith [hepsilon.trans hsmall]
  have hNeta (k : ℕ) : (N k).epsilon ≤ eta := by rw [hepsN]; exact hepseta
  let R := fun k => (N k).restrict_m28 eta (hNeta k) hetahalf
  have hinv : eta⁻¹ ≤ 3 * epsilon⁻¹ / 4 := by
    have heq : eta⁻¹ = (2 / 3 : ℝ) * epsilon⁻¹ := by
      dsimp only [eta]
      field_simp [hepspos.ne']
    rw [heq]
    nlinarith [inv_pos.mpr hepspos]
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  have hcap : ∀ᶠ k in atTop, (R k).carrier ⊆ (e k).target ∧
      ∀ x ∈ (R k).carrier, (e k).symm x ∈ G.exhaustion j := by
    filter_upwards [hj] with k hk
    have hfixed : (R k).carrier ⊆
        (fun x => (G.embedding k x).val.val) '' G.exhaustion j := by
      intro x hx
      change x ∈ (N k).carrier ∧
        ((N k).coordinate_inverse x).2 ∈ Ioo (-eta⁻¹) eta⁻¹ at hx
      apply hk.2 x hx.1
      rw [hepsN]
      exact (abs_lt.mpr hx.2).le.trans hinv
    constructor
    · rw [H.regularRawStageDiffeomorph_target]
      exact hfixed.trans (image_mono (hmono hk.1))
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hfixed hx
      have hys : y ∈ (e k).source := by
        rw [H.regularRawStageDiffeomorph_source]
        exact hmono hk.1 hy
      have hey : e k y = x := hyx
      have hxy : (e k).symm x = y :=
        (congrArg (e k).symm hey).symm.trans ((e k).left_inv hys)
      exact hxy.symm ▸ hy
  obtain ⟨F, Cset, hF, hcover⟩ := G.exists_finite_stage_chart_cover j
  let S := {q : G.limitCarrier.carrier // q ∈ F}
  let q : S → G.limitCarrier.carrier := Subtype.val
  let Kset := fun l : S => (extChartAt (𝓡 3) (q l)) '' Cset (q l)
  have hK (l : S) : IsCompact (Kset l) := (hF l.1 l.2).2.2.2.2.1
  have htarget (l : S) : Kset l ⊆ (extChartAt (𝓡 3) (q l)).target :=
    (hF l.1 l.2).2.2.2.2.2
  have hstage (l : S) (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ Kset l) :
      (extChartAt (𝓡 3) (q l)).symm y ∈ G.exhaustion (j + 1) := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hc := (hF l.1 l.2).2.2.2.1 hx
    rw [(extChartAt (𝓡 3) (q l)).left_inv hc.1]
    exact hc.2
  obtain ⟨a, b, B, ha, _, _, hbounds⟩ :=
    H.exists_eventual_regularRawStage_finite_chart_bounds W.tube W.radius W.radius_pos
      W.high_index G q Kset (j + 1) hK htarget hstage (n + 1)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hcap.and hbounds)
  let J := {v : ℕ × RoundCylinderSpace × S // K₀ ≤ v.1 ∧
    v.2.1.2 ∈ Ioo (-eta⁻¹) eta⁻¹ ∧
    (e v.1).symm ((N v.1).coordinate_map v.2.1) ∈ Cset (q v.2.2)}
  let y := fun i : J => capturedCylinderCoordinates (e i.1.1) (R i.1.1)
    i.1.2.1.1 i.1.2.1.2 (q i.1.2.2) 0
  have hy (i : J) : y i ∈ Kset i.1.2.2 := by
    change (extChartAt (𝓡 3) (q i.1.2.2))
      ((e i.1.1).symm (cylinderNeckChart (R i.1.1) i.1.2.1.1 i.1.2.1.2 0)) ∈ _
    rw [cylinderNeckChart_zero]
    exact mem_image_of_mem _ i.2.2.2
  have hp (i : J) : (e i.1.1).symm ((R i.1.1).coordinate_map i.1.2.1) ∈
      (extChartAt (𝓡 3) (q i.1.2.2)).source :=
    ((hF i.1.2.2.1 i.1.2.2.2).2.2.2.1 i.2.2.2).1
  have hs (i : J) : i.1.2.1.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    Proofs.M28.NeckAnalysis.cylinderStrip_mono hepspos hepseta i.2.2.1
  have hAj := H.hasUniformJetBoundsAt_normalizedSlice_initial_coefficients W.tube
    (fun i : J => idx i.1.1) (fun i => i.1.2.1.1) (fun i => i.1.2.1.2) hs (n + 1) hn
  have hBj : HasUniformJetBoundsAt (n + 1)
      (fun i : J => (H.normalizedSliceMetric (idx i.1.1)).pullbackCoefficients
        (e i.1.1 ∘ (extChartAt (𝓡 3) (q i.1.2.2)).symm)) y := by
    intro r hr
    exact ⟨B, fun i => ((hK₀ i.1.1 i.2.1).2 i.1.2.2 (y i) (hy i)).2 r hr⟩
  have hsource : 0 < ((4 * max C 2)⁻¹) ^ 2 * (1 - epsilon) := by
    have hC : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
    have hε : 0 < 1 - epsilon := by linarith [hepsilon.trans hsmall]
    positivity
  have hmap := hasUniformJetBoundsAt_capturedCylinderCoordinates_fderiv
    (fun i : J => H.normalizedSliceMetric (idx i.1.1)) (fun i => e i.1.1)
    (fun i => R i.1.1) (fun i => (hK₀ i.1.1 i.2.1).1.1)
    (fun i => i.1.2.1.1) (fun i => i.1.2.1.2) (fun i => q i.1.2.2)
    (fun i => i.2.2.1) hp n hAj hBj hsource ha
    (fun i v => H.normalizedSlice_initial_coefficient_lower W.tube (idx i.1.1)
      i.1.2.1.1 (hs i) v)
    (fun i v => ((hK₀ i.1.1 i.2.1).2 i.1.2.2 (y i) (hy i)).1 v |>.1)
  have herror : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i : J, K ≤ i.1.1 →
      ∀ r ≤ n + 1, ‖iteratedFDeriv ℝ r
          ((H.normalizedSliceMetric (idx i.1.1)).pullbackCoefficients
            (e i.1.1 ∘ (extChartAt (𝓡 3) (q i.1.2.2)).symm)) (y i) -
        iteratedFDeriv ℝ r
          (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i.1.2.2)).symm) (y i)‖ ≤
            delta := by
    intro delta hdelta
    obtain ⟨K, htail⟩ := eventually_atTop.mp
      (H.eventually_regularRawStage_finite_chart_jet_error W.tube W.radius W.radius_pos
        W.high_index G q Kset (j + 1) hK htarget hstage (n + 1) delta hdelta)
    exact ⟨K, fun i hi r hr => htail i.1.1 hi i.1.2.2 (y i) (hy i) r hr⟩
  have htail := exists_capturedCylinder_metric_error_tail G.limitMetric
    (fun i : J => H.normalizedSliceMetric (idx i.1.1)) (fun i => e i.1.1)
    (fun i => R i.1.1) (fun i => (hK₀ i.1.1 i.2.1).1.1)
    (fun i => i.1.2.1.1) (fun i => i.1.2.1.2) (fun i => q i.1.2.2)
    (fun i => i.2.2.1) hp (n + 1) (fun i => i.1.1) hmap herror
  intro rho hrho
  obtain ⟨K, htailK⟩ := htail rho hrho
  refine ⟨max K₀ K, ?_⟩
  intro k hk z hz r hr
  have hk₀ : K₀ ≤ k := (le_max_left _ _).trans hk
  have hzR : (R k).coordinate_map z ∈ (R k).carrier :=
    (R k).coordinate_map_mem_of_axial z hz
  have hzstage := (hK₀ k hk₀).1.2 _ hzR
  obtain ⟨q₀, hq₀⟩ := mem_iUnion.mp (hcover (subset_closure hzstage))
  obtain ⟨hqF, hqC⟩ := mem_iUnion.mp hq₀
  let l : S := ⟨q₀, hqF⟩
  let i : J := ⟨(k, z, l), hk₀, hz, interior_subset hqC⟩
  exact htailK i ((le_max_right _ _).trans hk) r hr

end PoincareConjecture.M28.CounterexampleNeckFamily
