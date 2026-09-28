import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapBall
import PoincareConjecture.Proofs.M35.CapGeometry.CurvatureRadius
import PoincareConjecture.Proofs.M35.CapGeometry.RadialNormalization










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization



theorem blowupSequence_normalized_ball_retained
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {r : ℝ} (hr : 0 < r) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G : RiemannianMetric 3 StandardCapSpace :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
      let phi : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      G.ball (x (L.subsequence k)) r ⊆
        phi '' (L.limit.flow.metric 0).ball L.limit.base (2 * r) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  let g := L.limit.flow.metric 0
  let K : Set L.limit.sliceCarrier.carrier := closure (g.ball L.limit.base (3 * r))
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball g
    (L.limit.complete 0 L.limit.zero_mem) L.limit.base (3 * r)
  obtain ⟨j, hj⟩ := hK.elim_directed_cover L.exhaustion.space L.exhaustion.space_open
    (fun z _ => by rw [L.exhaustion.space_covers]; exact mem_univ z)
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  have hball : closure (g.ball L.limit.base (2 * r)) ⊆ interior K := by
    let : MetricSpace L.limit.carrier.carrier := Proofs.M09.selectedMetricSpace g
    have hopen : IsOpen (g.ball L.limit.base (3 * r)) := by
      change IsOpen {z | edist L.limit.base z < ENNReal.ofReal (3 * r)}
      exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
    have hinner : g.ball L.limit.base (3 * r) ⊆ interior K :=
      hopen.subset_interior_iff.mpr subset_closure
    apply Subset.trans _ hinner
    rw [riemannian_closure_ball g L.limit.base (by positivity : 0 < 2 * r)]
    intro z hz
    change g.edist L.limit.base z < ENNReal.ofReal (3 * r)
    rw [← Proofs.M09.selectedMetricSpace_edist g, edist_dist, dist_comm,
      ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 3 * r)]
    exact (Metric.mem_closedBall.mp hz).trans_lt (by linarith only [hr])
  obtain ⟨N, _hjN, hretain⟩ := blowupSequence_ball_retention
    P E t x ht hR L j K hK hj (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop N] with k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let gk := E.flow.metric (t (L.subsequence k))
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric gk Q hQ
  let phi (z : L.limit.sliceCarrier.carrier) := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  have hbase : phi L.limit.base = x (L.subsequence k) :=
    congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val)
      (L.base_preserving k _)
  have hscaled := M13.homothety_ball_image gk G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety gk Q hQ) (x (L.subsequence k)) (r / Real.sqrt Q)
  have hroot : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hradius : Real.sqrt Q * (r / Real.sqrt Q) = r := by field_simp
  change id '' gk.ball (x (L.subsequence k)) (r / Real.sqrt Q) =
    G.ball (x (L.subsequence k)) (Real.sqrt Q * (r / Real.sqrt Q)) at hscaled
  rw [image_id, hradius] at hscaled
  have hsmall : r / Real.sqrt Q ≤ 2 * r / Real.sqrt (Q / (1 - 1 / 2)) := by
    rw [show Q / (1 - 1 / 2) = 2 * Q by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hQ)
      (mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
        (Real.sqrt_pos.mpr hQ))).mpr
    have htwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith only [mul_le_mul_of_nonneg_right htwo (mul_nonneg hr.le (Real.sqrt_nonneg Q))]
  change G.ball (x (L.subsequence k)) r ⊆ phi '' g.ball L.limit.base (2 * r)
  intro y hy
  apply hretain k hk L.limit.base (2 * r) (by positivity) hball
  change y ∈ gk.ball (phi L.limit.base) (2 * r / Real.sqrt (Q / (1 - 1 / 2)))
  rw [hbase]
  have hy' : y ∈ gk.ball (x (L.subsequence k)) (r / Real.sqrt Q) := by
    rw [hscaled]
    exact hy
  exact hy'.trans_le (ENNReal.ofReal_le_ofReal hsmall)

end PoincareConjecture.M35.OrdinaryRealization
