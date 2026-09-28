import PoincareConjecture.Proofs.M35.CapGeometry.SelectedBoundaryPatch
import PoincareConjecture.Proofs.M35.CapGeometry.BoundaryNeckRadius
import PoincareConjecture.Proofs.M35.CapGeometry.TransportedInnerBall
import PoincareConjecture.Proofs.M35.Thm12_28.CompactMetricComparison

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem blowupSequence_cap_boundary_curvature_ball_neighborhoods
    (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {g₀ : StandardInitialMetric}
      (E : RepairedStandardCapExistenceData g₀)
      (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
      (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
        (blowupBackwardInterval ⊤)) (j : ℕ),
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
      ∀ N : CapCertificate (L.limit.flow.metric 0), N.epsilon ≤ delta →
        IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
        ∀ y ∈ N.boundary_sphere, ∃ V : Set L.limit.carrier.carrier,
          IsOpen V ∧ y ∈ V ∧ ∀ᶠ k in atTop, ∀ w ∈ V,
            let f : L.limit.sliceCarrier.carrier → StandardCapSpace := fun z =>
              ((L.embedding k).forward 0
                ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
            ∃ r : ℝ, 0 < r ∧
              scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
                (E.flow.connection (t (L.subsequence k)))
                  ((E.flow.metric (t (L.subsequence k))).ball (f w) r) = r⁻¹ ^ 2 ∧
              closure ((E.flow.metric (t (L.subsequence k))).ball (f w) r) ⊆ f '' N.carrier ∧
              IsCompact (closure ((E.flow.metric (t (L.subsequence k))).ball (f w) r)) := by
  obtain ⟨delta₀, hdelta₀, hscalar⟩ := exists_scaled_nonnegative_cylinder_scalar_floor P.curvature
  let epsilon := min delta₀ (1 / 100)
  have he : 0 < epsilon := lt_min hdelta₀ (by norm_num)
  have hesmall : epsilon ≤ 1 / 24 := (min_le_right _ _).trans (by norm_num)
  have helong : 8 < epsilon⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ he]
    have h := min_le_right delta₀ (1 / 100 : ℝ)
    dsimp only [epsilon]
    nlinarith
  refine ⟨epsilon / 4, div_pos he (by norm_num), ?_⟩
  intro g₀ E t x ht hR L j
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N hfine hcompact hU y hy
  let : MetricSpace L.limit.carrier.carrier :=
    Proofs.M09.selectedMetricSpace (L.limit.flow.metric 0)
  have hballEq (r : ℝ) (hr : 0 < r) :
      (L.limit.flow.metric 0).ball y r = Metric.ball y r := by
    ext z
    change (L.limit.flow.metric 0).edist y z < ENNReal.ofReal r ↔ dist z y < r
    rw [← Proofs.M09.selectedMetricSpace_edist (L.limit.flow.metric 0), edist_dist, dist_comm]
    exact ENNReal.ofReal_lt_ofReal_iff hr
  obtain ⟨r₀, hr₀, hball₀⟩ :=
    Metric.mem_nhds_iff.mp (N.carrier_open.mem_nhds (N.boundary_subset hy))
  let S := N.boundary_neck.scale⁻¹ ^ 2
  have hS : 0 < S := sq_pos_of_pos (inv_pos.mpr N.boundary_neck.scale_pos)
  let d := min r₀ (1 / (4 * Real.sqrt S))
  have hd : 0 < d := lt_min hr₀ (by positivity)
  let V := Metric.ball y d
  have hinner : (L.limit.flow.metric 0).ball y d ⊆ N.carrier := by
    rw [hballEq d hd]
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans hball₀
  obtain ⟨km, hjm, hmetric⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j (closure N.carrier) hcompact hU 3 (by norm_num)
  have hstage : closure N.boundary_neck.carrier ⊆ L.exhaustion.space j :=
    (closure_mono N.boundary_neck_subset).trans hU
  have hde : N.boundary_neck.epsilon ≤ epsilon / 4 := by
    rw [N.boundary_neck_epsilon]
    exact hfine
  have hpatch := blowupSequence_boundary_neck_patch P E.atlas E t x ht hR L
    N.boundary_neck j hstage epsilon he hde
  have hycentral : y ∈ N.boundary_neck.central_sphere := N.boundary_eq_neck_sphere ▸ hy
  obtain ⟨⟨q, s⟩, hs, hpoint⟩ := N.boundary_neck.central_sphere_eq ▸ hycentral
  have hs0 : s = 0 := hs.2
  subst s
  refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self hd, ?_⟩
  filter_upwards [eventually_ge_atTop km, hpatch] with k hkm hkpatch
  intro w hw
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  let f : L.limit.carrier.carrier → StandardCapSpace := fun z =>
    ((L.embedding k).forward 0 hzero z).val
  have hsource : N.carrier ⊆ phi.source := fun z hz =>
    L.exhaustion.space_increasing (hjm.trans hkm) (hU (subset_closure hz))
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f N.carrier := phi.contMDiffOn_toFun.mono hsource
  have hnorm (z : L.limit.carrier.carrier) (hz : z ∈ N.carrier)
      (v : TangentSpace (𝓡 3) z) :
      (E.flow.metric (t (L.subsequence k))).tangentNorm (f z)
          (mfderiv (𝓡 3) (𝓡 3) f z v) ≤
        (2 / Real.sqrt Q) * (L.limit.flow.metric 0).tangentNorm z v := by
    have h := (abs_le.mp (hmetric k hkm z (subset_closure hz) v)).2
    change Q * (E.flow.metric (t (L.subsequence k))).inner (f z)
        (mfderiv (𝓡 3) (𝓡 3) f z v) (mfderiv (𝓡 3) (𝓡 3) f z v) -
      (L.limit.flow.metric 0).inner z v v ≤ 3 * (L.limit.flow.metric 0).inner z v v at h
    have hbound := M35.tangentNorm_pullback_le_of_quadratic_le (L.limit.flow.metric 0)
      (E.flow.metric (t (L.subsequence k))) f z v hQ (by norm_num : (0 : ℝ) ≤ 4)
      (by linarith)
    rw [Real.sqrt_div (by norm_num) Q] at hbound
    norm_num at hbound
    exact hbound
  have hmap := M35.image_ball_subset_of_tangentNorm_upper (L.limit.flow.metric 0)
    (E.flow.metric (t (L.subsequence k))) f N.carrier_open hf
    (div_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hQ)) y hinner hnorm
  have hwball : w ∈ (L.limit.flow.metric 0).ball y d := (hballEq d hd).symm ▸ hw
  have hclosepoint := hmap ⟨w, hwball, rfl⟩
  have hradius : (2 / Real.sqrt Q) * d ≤ 1 / (2 * Real.sqrt (S * Q)) := by
    have hmul := mul_le_mul_of_nonneg_left (min_le_right r₀ (1 / (4 * Real.sqrt S)))
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg Q))
    have heq : (2 / Real.sqrt Q) * (1 / (4 * Real.sqrt S)) =
        1 / (2 * Real.sqrt (S * Q)) := by
      rw [Real.sqrt_mul hS.le]
      field_simp
      ring
    exact hmul.trans_eq heq
  obtain ⟨patch, hcoord, hcarrier, hclose⟩ := hkpatch
  have hpoint' : patch.coordinate (q, 0) = f y := by
    rw [hcoord]
    exact congrArg f hpoint
  have hnear : f w ∈ (E.flow.metric (t (L.subsequence k))).ball
      (patch.coordinate (q, 0)) (1 / (2 * Real.sqrt (S * Q))) := by
    rw [hpoint']
    exact hclosepoint.trans_le (ENNReal.ofReal_le_ofReal hradius)
  have hfloor := hscalar epsilon he (min_le_left _ _) E.atlas
    (E.flow.metric (t (L.subsequence k))) (E.flow.connection (t (L.subsequence k)))
    (S * Q) (mul_pos hS hQ) _ patch q hclose
    (E.nonnegative_sectional _ (ht (L.subsequence k)) _)
  have hRcont : Continuous (E.flow.connection (t (L.subsequence k))).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature
      (E.flow.connection (t (L.subsequence k)))).continuous
  obtain ⟨r, hr, _, hscale, hcontained, hcompactr⟩ :=
    patch.exists_curvature_radius_near_central_sphere E.atlas
      (E.flow.metric (t (L.subsequence k))) (E.flow.connection (t (L.subsequence k)))
      (E.complete _ (ht (L.subsequence k))) hRcont (S * Q) (mul_pos hS hQ)
      he hesmall helong hclose q hfloor (f w) hnear
  exact ⟨r, hr, hscale,
    hcontained.trans (hcarrier.trans (image_mono N.boundary_neck_subset)), hcompactr⟩

end PoincareConjecture.M35.OrdinaryRealization
