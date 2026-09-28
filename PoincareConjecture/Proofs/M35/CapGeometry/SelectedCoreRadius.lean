import PoincareConjecture.Proofs.M35.CapGeometry.BufferedRadius
import PoincareConjecture.Proofs.M35.CapGeometry.TransportedInnerBall
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapBall
import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem exists_metric_margin {r a b : ℝ} (hr : 0 < r)
    (hra : r < a) (hab : a < b) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      Real.sqrt (1 + eta) * r < a ∧ a < b * Real.sqrt (1 - eta) := by
  have ha : 0 < a := hr.trans hra
  have hb : 0 < b := ha.trans hab
  have hra2 : r ^ 2 < a ^ 2 := pow_lt_pow_left₀ hra hr.le (by omega)
  have hab2 : a ^ 2 < b ^ 2 := pow_lt_pow_left₀ hab ha.le (by omega)
  let eta := min (1 / 2) (min ((a ^ 2 - r ^ 2) / (2 * r ^ 2))
    ((b ^ 2 - a ^ 2) / (2 * b ^ 2)))
  have he : 0 < eta := lt_min (by norm_num)
    (lt_min (div_pos (sub_pos.mpr hra2) (by positivity))
      (div_pos (sub_pos.mpr hab2) (by positivity)))
  have hehalf : eta ≤ 1 / 2 := min_le_left _ _
  have her : eta ≤ (a ^ 2 - r ^ 2) / (2 * r ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have heb : eta ≤ (b ^ 2 - a ^ 2) / (2 * b ^ 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have her' := (le_div_iff₀ (show 0 < 2 * r ^ 2 by positivity)).mp her
  have heb' := (le_div_iff₀ (show 0 < 2 * b ^ 2 by positivity)).mp heb
  have hsr : (Real.sqrt (1 + eta)) ^ 2 = 1 + eta := Real.sq_sqrt (by positivity)
  have hsb : (Real.sqrt (1 - eta)) ^ 2 = 1 - eta := Real.sq_sqrt (by linarith)
  refine ⟨eta, he, by linarith, ?_, ?_⟩
  · nlinarith [sq_nonneg (a - Real.sqrt (1 + eta) * r),
      mul_nonneg (Real.sqrt_nonneg (1 + eta)) hr.le]
  · nlinarith [sq_nonneg (b * Real.sqrt (1 - eta) - a),
      mul_nonneg hb.le (Real.sqrt_nonneg (1 - eta))]

private theorem closure_ball_subset_larger {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M] (g : RiemannianMetric 3 M)
    (y : M) {r b : ℝ} (hr : 0 < r) (hrb : r < b) :
    closure (g.ball y r) ⊆ g.ball y b := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  rw [M35.riemannian_closure_ball g y hr]
  intro z hz
  change g.edist y z < ENNReal.ofReal b
  rw [← Proofs.M09.selectedMetricSpace_edist g, edist_dist, dist_comm]
  exact (ENNReal.ofReal_lt_ofReal_iff (hr.trans hrb)).mpr
    ((Metric.mem_closedBall.mp hz).trans_lt hrb)




theorem blowupSequence_scalar_witness_curvature_balls (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∀ Y : Set L.limit.carrier.carrier, ∀ r a b : ℝ, 0 < r → r < a → a < b →
      ∀ z ∈ N.carrier, 1 < a ^ 2 * N.connection.scalarCurvature z →
      (∀ y ∈ Y, z ∈ (L.limit.flow.metric 0).ball y r ∧
        closure ((L.limit.flow.metric 0).ball y b) ⊆ N.carrier) →
      ∀ᶠ k in atTop, ∀ y ∈ Y,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∃ r : ℝ, 0 < r ∧
          scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
            (E.flow.connection (t (L.subsequence k)))
              ((E.flow.metric (t (L.subsequence k))).ball (f y) r) = r⁻¹ ^ 2 ∧
          closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r) ⊆ f '' N.carrier ∧
          IsCompact (closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N hconnection hcompact hU Y r a b hr hra hab z hzU hcross hgeometry
  have ha : 0 < a := hr.trans hra
  have hb : 0 < b := ha.trans hab
  obtain ⟨eta, heta, heta1, hinner, houter⟩ := exists_metric_margin hr hra hab
  let delta := (a ^ 2 * N.connection.scalarCurvature z - 1) / (2 * a ^ 2)
  have hdelta : 0 < delta := div_pos (sub_pos.mpr hcross) (by positivity)
  obtain ⟨km, hjm, hmetric⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j (closure N.carrier) hcompact hU eta heta
  obtain ⟨ks, _, hscalar⟩ := blowupSequence_terminal_scalar_uniform_compact
    P E t x ht hR L j (closure N.carrier) hcompact hU delta hdelta
  obtain ⟨kb, _, hball⟩ := blowupSequence_ball_retention
    P E t x ht hR L j (closure N.carrier) hcompact hU heta heta1
  filter_upwards [eventually_ge_atTop (max km (max ks kb))] with k hk
  intro y hy
  obtain ⟨hz, hbuffer⟩ := hgeometry y hy
  have hinner_ball : (L.limit.flow.metric 0).ball y r ⊆ N.carrier := by
    intro w hw
    exact hbuffer (subset_closure (hw.trans_le (ENNReal.ofReal_le_ofReal (hra.trans hab).le)))
  have hkm : km ≤ k := by omega
  have hks : ks ≤ k := by omega
  have hkb : kb ≤ k := by omega
  have hjk : j ≤ k := hjm.trans hkm
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have hQsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let q := a / Real.sqrt Q
  have hq : 0 < q := div_pos ha hQsqrt
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  let f : L.limit.carrier.carrier → StandardCapSpace := fun w =>
    ((L.embedding k).forward 0 hzero w).val
  have hsource : N.carrier ⊆ phi.source := fun w hw =>
    L.exhaustion.space_increasing hjk (hU (subset_closure hw))
  have hRcont : Continuous (E.flow.connection (t (L.subsequence k))).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature
      (E.flow.connection (t (L.subsequence k)))).continuous
  have hcomplete := E.complete (t (L.subsequence k)) (ht (L.subsequence k))
  have hnorm (w : L.limit.carrier.carrier) (hw : w ∈ N.carrier)
      (v : TangentSpace (𝓡 3) w) :
      (E.flow.metric (t (L.subsequence k))).tangentNorm (f w)
          (mfderiv (𝓡 3) (𝓡 3) f w v) ≤
        Real.sqrt ((1 + eta) / Q) * (L.limit.flow.metric 0).tangentNorm w v := by
    apply M35.tangentNorm_pullback_le_of_quadratic_le (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) f w v hQ (by positivity)
    have h := (abs_le.mp (hmetric k hkm w (subset_closure hw) v)).2
    change Q * (E.flow.metric (t (L.subsequence k))).inner (f w)
        (mfderiv (𝓡 3) (𝓡 3) f w v) (mfderiv (𝓡 3) (𝓡 3) f w v) -
      (L.limit.flow.metric 0).inner w v v ≤ eta * (L.limit.flow.metric 0).inner w v v at h
    linarith
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f N.carrier :=
    phi.contMDiffOn_toFun.mono hsource
  have hinnerQ : Real.sqrt ((1 + eta) / Q) * r < q := by
    rw [Real.sqrt_div (by positivity) Q, div_mul_eq_mul_div]
    exact (div_lt_div_iff_of_pos_right hQsqrt).mpr hinner
  have hzball : f z ∈ (E.flow.metric (t (L.subsequence k))).ball (f y) q := by
    have hzsmall := M35.image_ball_subset_of_tangentNorm_upper (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) f N.carrier_open hf
      (Real.sqrt_pos.mpr (div_pos (by positivity) hQ)) y
      hinner_ball hnorm ⟨z, hz, rfl⟩
    exact hzsmall.trans_le (ENNReal.ofReal_le_ofReal hinnerQ.le)
  have hscalarZ := hscalar k hks z (subset_closure hzU)
  rw [← hconnection] at hscalarZ
  have hcrossQ : 1 < a ^ 2 *
      ((E.flow.connection (t (L.subsequence k))).scalarCurvature (f z) / Q) := by
    have hd : delta * (2 * a ^ 2) = a ^ 2 * N.connection.scalarCurvature z - 1 :=
      div_mul_cancel₀ _ (by positivity)
    have herr := (abs_lt.mp hscalarZ).1
    have hmul := mul_lt_mul_of_pos_left herr (sq_pos_of_pos ha)
    change _ < _ at hmul
    nlinarith
  have hsup : (E.flow.connection (t (L.subsequence k))).scalarCurvature (f z) ≤
      scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
        (E.flow.connection (t (L.subsequence k)))
          ((E.flow.metric (t (L.subsequence k))).ball (f y) q) := by
    apply le_csSup (a := (E.flow.connection (t (L.subsequence k))).scalarCurvature (f z))
      (show BddAbove (range fun w : (E.flow.metric (t (L.subsequence k))).ball (f y) q =>
        (E.flow.connection (t (L.subsequence k))).scalarCurvature w.1) from ?_)
      ⟨⟨f z, hzball⟩, rfl⟩
    have hc := Proofs.M09.isCompact_closure_metric_ball
      (E.flow.metric (t (L.subsequence k))) hcomplete (f y) q
    rw [← image_eq_range]
    exact (hc.bddAbove_image hRcont.continuousOn).mono (image_mono subset_closure)
  have hqscale : q ^ 2 = a ^ 2 / Q := by
    rw [div_pow, Real.sq_sqrt hQ.le]
  have hcrossTarget : 1 ≤ q ^ 2 *
      scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
        (E.flow.connection (t (L.subsequence k)))
          ((E.flow.metric (t (L.subsequence k))).ball (f y) q) := by
    have h := mul_le_mul_of_nonneg_left hsup (sq_nonneg q)
    have hleft : q ^ 2 *
        (E.flow.connection (t (L.subsequence k))).scalarCurvature (f z) =
      a ^ 2 * ((E.flow.connection (t (L.subsequence k))).scalarCurvature (f z) / Q) := by
      rw [hqscale]
      ring
    rw [hleft] at h
    exact hcrossQ.le.trans h
  have hretained := hball k hkb y b hb
    (hbuffer.trans (N.carrier_open.subset_interior_iff.mpr subset_closure))
  have houterQ : q < b / Real.sqrt (Q / (1 - eta)) := by
    rw [Real.sqrt_div hQ.le, div_div_eq_mul_div]
    exact (div_lt_div_iff_of_pos_right hQsqrt).mpr houter
  have hinside : closure ((E.flow.metric (t (L.subsequence k))).ball (f y) q) ⊆
      f '' N.carrier :=
    ((closure_ball_subset_larger _ _ hq houterQ).trans hretained).trans
      (image_mono (subset_closure.trans hbuffer))
  obtain ⟨r, hrpos, hrq, hrexact, hrcompact⟩ := M35.exists_scalar_curvature_radius_le
    (E.flow.metric (t (L.subsequence k))) (E.flow.connection (t (L.subsequence k)))
      hcomplete hRcont (f y) hq hcrossTarget
  refine ⟨r, hrpos, hrexact, ?_, hrcompact⟩
  exact (closure_mono (fun w hw => hw.trans_le (ENNReal.ofReal_le_ofReal hrq))).trans hinside




theorem blowupSequence_cap_core_curvature_ball_at (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∀ y ∈ N.core, ∀ᶠ k in atTop,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∃ r : ℝ, 0 < r ∧
          scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
            (E.flow.connection (t (L.subsequence k)))
              ((E.flow.metric (t (L.subsequence k))).ball (f y) r) = r⁻¹ ^ 2 ∧
          closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r) ⊆ f '' N.carrier ∧
          IsCompact (closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N hconnection hcompact hU y hy
  obtain ⟨a, b, hra, hab, hbuffer, z, hz, hcross⟩ :=
    N.exists_buffered_core_scalar_witness hy
  have hzU := N.core_ball_subset y hy (subset_closure hz)
  have h := blowupSequence_scalar_witness_curvature_balls P E t x ht hR L j
    N hconnection hcompact hU {y} (N.core_radius y) a b (N.core_radius_pos y hy)
    hra hab z hzU hcross (by
      intro w hw
      rcases mem_singleton_iff.mp hw with rfl
      exact ⟨hz, hbuffer⟩)
  exact h.mono (fun _ hk => hk y (mem_singleton y))

end PoincareConjecture.M35.OrdinaryRealization
