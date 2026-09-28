import PoincareConjecture.Proofs.M35.CapGeometry.CompactCurvatureDerivative
import PoincareConjecture.Proofs.M35.CapGeometry.CurvatureRadius
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapBall










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => EuclideanSpace ℝ (Fin 3)



theorem blowupSequence_curvature_derivative_bounded_ball_of_chart
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set V) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (r : ℝ) (hr : 0 < r) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    closure ((L.limit.flow.metric 0).ball L.limit.base r) ⊆
      interior ((extChartAt (𝓡 3) q).symm '' K) →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      ∀ y ∈ RiemannianMetric.ball
        (M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ)
          (x (L.subsequence k)) (r / 2),
        (M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k)))
          Q hQ).curvatureDerivativeNorm 1 y ≤ B := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro hball
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  let C : Set L.limit.sliceCarrier.carrier := c.symm '' K
  have hC : IsCompact C := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm (show L.limit.carrier.carrier from q)).mono
      (fun _ hz => (hKU hz).1))
  have hCU : C ⊆ L.exhaustion.space j := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hKU hp).2
  obtain ⟨B, hB, N, _hjN, hbound⟩ :=
    blowupSequence_terminal_curvature_derivative_bounded_chart P E t x ht hR L q j K hK hKU
  obtain ⟨N', _hjN', hretain⟩ := blowupSequence_ball_retention
    P E t x ht hR L j C hC hCU (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop (max N N')] with k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let g := E.flow.metric (t (L.subsequence k))
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g Q hQ
  let phi (z : L.limit.sliceCarrier.carrier) := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  have hbase : phi L.limit.base = x (L.subsequence k) := by
    exact congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val)
      (L.base_preserving k _)
  have hscaled := M13.homothety_ball_image g G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) (x (L.subsequence k)) ((r / 2) / Real.sqrt Q)
  have hroot : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hradius : Real.sqrt Q * ((r / 2) / Real.sqrt Q) = r / 2 := by
    field_simp
  change id '' g.ball (x (L.subsequence k)) ((r / 2) / Real.sqrt Q) =
    G.ball (x (L.subsequence k)) (Real.sqrt Q * ((r / 2) / Real.sqrt Q)) at hscaled
  rw [image_id, hradius] at hscaled
  have hsmall : (r / 2) / Real.sqrt Q ≤ r / Real.sqrt (Q / (1 - 1 / 2)) := by
    have hden : Q / (1 - 1 / 2) = 2 * Q := by ring
    rw [hden, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_div]
    apply div_le_div_of_nonneg_left hr.le
      (mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) (Real.sqrt_pos.mpr hQ))
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg Q)
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  change ∀ y ∈ G.ball (x (L.subsequence k)) (r / 2),
    (M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k)))
      Q hQ).curvatureDerivativeNorm 1 y ≤ B
  intro y hy
  have hy' : y ∈ g.ball (phi L.limit.base) (r / Real.sqrt (Q / (1 - 1 / 2))) := by
    rw [hbase]
    have hysmall : y ∈ g.ball (x (L.subsequence k)) ((r / 2) / Real.sqrt Q) := by
      rw [hscaled]
      exact hy
    exact hysmall.trans_le (ENNReal.ofReal_le_ofReal hsmall)
  obtain ⟨z, hz, hzy⟩ := hretain k ((le_max_right N N').trans hk) L.limit.base r hr hball hy'
  have hzC : z ∈ C := interior_subset (hball (subset_closure hz))
  obtain ⟨p, hp, hpz⟩ := hzC
  have h := hbound k ((le_max_left N N').trans hk) p hp
  change (M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k)))
    Q hQ).curvatureDerivativeNorm 1 (phi (c.symm p)) ≤ B at h
  change phi z = y at hzy
  rwa [hpz, hzy] at h



theorem blowupSequence_exists_curvature_derivative_ball_bound
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    ∃ d B : ℝ, 0 < d ∧ 0 < B ∧ ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      ∀ y ∈ RiemannianMetric.ball
        (M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ)
          (x (L.subsequence k)) d,
        (M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k)))
          Q hQ).curvatureDerivativeNorm 1 y ≤ B := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  let q := L.limit.base
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  let U := c.target ∩ c.symm ⁻¹' L.exhaustion.space 0
  have hU : IsOpen U := (continuousOn_extChartAt_symm
    (show L.limit.carrier.carrier from q)).isOpen_inter_preimage
      (isOpen_extChartAt_target (show L.limit.carrier.carrier from q))
      (L.exhaustion.space_open 0)
  have hqU : c q ∈ U := by
    refine ⟨mem_extChartAt_target (show L.limit.carrier.carrier from q), ?_⟩
    change c.symm (c q) ∈ L.exhaustion.space 0
    rw [c.left_inv (mem_extChartAt_source (show L.limit.carrier.carrier from q))]
    exact L.exhaustion.base_mem 0
  obtain ⟨K, hK, hqK, hKU⟩ := exists_compact_between isCompact_singleton hU
    (singleton_subset_iff.mpr hqU)
  let W := c.source ∩ c ⁻¹' interior K
  have hccont : ContinuousOn c c.source := by
    have hsource := extChartAt_source (𝓡 3) (show L.limit.carrier.carrier from q)
    rw [hsource]
    exact (contMDiffOn_extChartAt (I := 𝓡 3) (n := ∞)
      (x := (show L.limit.carrier.carrier from q))).continuousOn
  have hW : IsOpen W := hccont.isOpen_inter_preimage
    (isOpen_extChartAt_source (show L.limit.carrier.carrier from q)) isOpen_interior
  have hqW : q ∈ W :=
    ⟨mem_extChartAt_source (show L.limit.carrier.carrier from q), hqK (mem_singleton _)⟩
  have hWK : W ⊆ c.symm '' K := by
    intro z hz
    exact ⟨c z, interior_subset hz.2, c.left_inv hz.1⟩
  have hqint : q ∈ interior (c.symm '' K) := (hW.subset_interior_iff.mpr hWK) hqW
  let g := L.limit.flow.metric 0
  let : MetricSpace L.limit.carrier.carrier := Proofs.M09.selectedMetricSpace g
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hqint)
  have hclosure : closure (g.ball q (a / 2)) ⊆ interior (c.symm '' K) := by
    rw [riemannian_closure_ball g q (half_pos ha)]
    intro z hz
    apply hball
    exact (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self ha)
  obtain ⟨B, hB, hbound⟩ := blowupSequence_curvature_derivative_bounded_ball_of_chart
    P E t x ht hR L q 0 K hK hKU (a / 2) (half_pos ha) hclosure
  exact ⟨(a / 2) / 2, B, half_pos (half_pos ha), hB, hbound⟩

end PoincareConjecture.M35.OrdinaryRealization
