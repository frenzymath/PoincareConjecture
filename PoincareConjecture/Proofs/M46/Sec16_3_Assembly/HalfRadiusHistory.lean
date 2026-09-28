import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration
import PoincareConjecture.Proofs.M33.HistoryCylinderSource
import PoincareConjecture.Proofs.M33.GuardedCylinders
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction












set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

private theorem metric_center_mem {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x : M) {r : ℝ} (hr : 0 < r) : x ∈ g.ball x r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 n) x x < ENNReal.ofReal r
  simpa only [Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hr



theorem history_halfBall_compact {F : SurgeryFlowData.{u}}
    {W : M33RegularHistoryWindow F} (H : M33RegularHistoryData W)
    {t r : ℝ} (ht : t ∈ H.generalized.interval)
    (x : (H.generalized.slice t).carrier) (hr : 0 < r)
    (hretain : (F.metric t).ball (H.history.forward t ht x) r ⊆ m33RegularRegion F t) :
    IsCompact (closure ((H.generalized.metric t).ball x (r / 2))) := by
  have hfull : (F.metric t).ball (H.history.forward t ht x) r ⊆
      range (H.history.forward t ht) := by
    simpa only [H.regular_range] using hretain
  have hhalf : (F.metric t).ball (H.history.forward t ht x) (r / 2) ⊆
      range (H.history.forward t ht) := by
    intro y hy
    apply hfull
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hcompact : IsCompact
      (closure ((F.metric t).ball (H.history.forward t ht x) (r / 2))) :=
    (F.slices_compact t (W.time_subset (H.interval_eq ▸ ht))).of_isClosed_subset
      isClosed_closure (subset_univ _)
  have hsubset : closure ((F.metric t).ball (H.history.forward t ht x) (r / 2)) ⊆
      range (H.history.forward t ht) :=
    (M04.initial_half_ball_closure_subset_initial_ball (F.metric t)
      (H.history.forward t ht x) hr).trans hfull
  rw [(H.history.forward_openEmbedding t ht).isEmbedding.closure_eq_preimage_closure_image,
    H.history.ball_image_of_subset t ht x (r / 2) hhalf]
  exact (H.history.forward_openEmbedding t ht).isEmbedding.isInducing.isCompact_preimage'
    hcompact hsubset

private theorem history_point_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))



theorem halfRadiusHistory (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) : Nonempty (HalfRadiusHistory D) := by
  obtain ⟨R⟩ := P.regularSpacetime D.window
  have ht : D.time ∈ R.history.generalized.interval := by
    rw [R.history.interval_eq]
    exact ⟨D.cylinder.test_time_pos D.radius_pos |>.le, le_rfl⟩
  have hretain := D.cylinder.terminal_ball_regular D.center D.radius_pos D.based
  have hx := metric_center_mem (F.metric D.time) D.center D.radius_pos
  obtain ⟨x, hx⟩ : D.center ∈ range (R.history.history.forward D.time ht) := by
    rw [R.history.regular_range]
    exact hretain hx
  have hJ : Icc (-(D.radius / 2) ^ 2) 0 ⊆ Icc (-D.radius ^ 2) 0 := by
    intro s hs
    constructor
    · nlinarith [hs.1, sq_nonneg D.radius]
    · exact hs.2
  let U := (F.metric D.time).ball (R.history.history.forward D.time ht x) (D.radius / 2)
  have hU : U ⊆ (F.metric D.time).ball D.center D.radius := by
    intro y hy
    rw [← hx]
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (half_le_self D.radius_pos.le))
  let e := D.cylinder.restrict hJ ordConnected_Icc hU
  have htime (s : ℝ) (hs : s ∈ Icc (-(D.radius / 2) ^ 2) 0) :
      D.time + s / 1 ∈ R.history.generalized.interval := by
    rw [R.history.interval_eq]
    have hn := F.time_domain_nonnegative (e.time_subset ⟨s, hs, rfl⟩)
    exact ⟨hn, by simpa using hs.2⟩
  have hreg (s : ℝ) (hs : s ∈ Icc (-(D.radius / 2) ^ 2) 0) :
      e.forward s hs '' U ⊆
        m33RegularRegion F (D.time + s / 1) := by
    rintro y ⟨z, hz, rfl⟩
    exact (D.cylinder.regular_image_smaller_closed
      (half_pos D.radius_pos) (half_lt_self D.radius_pos) hs).choose_spec
        ⟨z, hU hz, rfl⟩
  obtain ⟨d, hd, _⟩ := R.history.cylinders_from_surgery (F.slice D.time) D.time 1
    (Icc (-(D.radius / 2) ^ 2) 0) U
    (M04.initial_ball_isOpen _ _ _) htime e hreg
  let c := R.history.history.rebaseCylinder D.time ht x (D.radius / 2) d
  have hmaps (y : (R.history.generalized.slice D.time).carrier)
      (hy : y ∈ (R.history.generalized.metric D.time).ball x (D.radius / 2)) :
      R.history.history.forward D.time ht y ∈ U :=
    R.history.history.ball_image_subset D.time ht x (D.radius / 2) ⟨y, hy, rfl⟩
  have hb : ∀ h y,
      y ∈ (R.history.generalized.metric D.time).ball x (D.radius / 2) →
      c.pointMap 0 h y = (⟨D.time, y⟩ : R.history.generalized.point) := by
    intro h y hy
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply history_point_heq R.history.history (htime 0 h) ht (by simp)
    exact (heq_of_eq (hd 0 h _ (hmaps y hy))).trans
      (D.based (hJ h) _ (hU (hmaps y hy)))
  have hc : ∀ s hs y,
      y ∈ (R.history.generalized.metric D.time).ball x (D.radius / 2) →
      R.history.generalized.curvatureNorm (c.pointMap s hs y) ≤ (D.radius / 2)⁻¹ ^ 2 := by
    intro s hs y hy
    have hp := R.history.curvature_norm_pullback (D.time + s / 1) (htime s hs)
      (d.forward s hs (R.history.history.forward D.time ht y))
    rw [hd s hs _ (hmaps y hy)] at hp
    change (R.history.generalized.connection (D.time + s / 1)).curvatureTensorNorm
      (d.forward s hs (R.history.history.forward D.time ht y)) ≤ _
    rw [← hp]
    apply (D.curvature s (hJ hs) _ (hU (hmaps y hy))).trans
    exact pow_le_pow_left₀ (inv_nonneg.mpr D.radius_pos.le)
      (inv_le_inv₀ D.radius_pos (half_pos D.radius_pos) |>.2
        (half_le_self D.radius_pos.le)) 2
  refine ⟨{
    spacetime := R
    time_mem := ht
    center := x
    center_eq := hx
    cylinder := c
    time_subset := ?_
    based := hb
    curvature := hc
    terminal_ball_compact := ?_
  }⟩
  · intro s hs
    have h := htime (s - D.time) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [div_one, add_sub_cancel] using h
  · have hcompact := history_halfBall_compact R.history ht x D.radius_pos
      (by simpa only [hx] using hretain)
    change IsCompact (closure
      ((R.geometry.realization.slices D.time).metricOnPoints.ball
        ((R.geometry.sliceIdentification D.time).identification x) (D.radius / 2)))
    rw [← M13.originalSlice_ball R.geometry P.m13 D.time x (D.radius / 2)]
    convert! hcompact.image (R.geometry.sliceIdentification D.time).identification.continuous
      using 1
    exact ((R.geometry.sliceIdentification D.time).identification.toHomeomorph.image_closure
      ((R.history.generalized.metric D.time).ball x (D.radius / 2))).symm

end PoincareConjecture.Proofs.M46
