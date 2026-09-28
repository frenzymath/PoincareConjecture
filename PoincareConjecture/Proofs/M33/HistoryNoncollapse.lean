import PoincareConjecture.Proofs.M33.HistoryCylinderSource
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M33.GuardedCylinders
import PoincareConjecture.Proofs.M04.ShiCarrier
import PoincareConjecture.Definitions.Ch16.ControlledSurgery

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W)

theorem M33RegularHistoryData.backward_time_subset
    {C : GeneralizedSliceCarrier.{u}} {t r : ℝ} {U : Set C.carrier}
    (ht : t ∈ H.generalized.interval)
    (e : SurgeryFlowCylinder F C t 1 (Ioc (-r ^ 2) 0) U)
    (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0) : t + s / 1 ∈ H.generalized.interval := by
  have hn := F.time_domain_nonnegative (e.time_subset ⟨s, hs, rfl⟩)
  rw [H.interval_eq] at ht ⊢
  exact W.interval_connected.out W.zero_mem ht ⟨hn, by simpa using hs.2⟩

private theorem history_point_heq {G : GeneralizedRicciFlowData.{u}}
    (D : M33RegularHistoryRealization G F) {s t : ℝ}
    (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (D.forward s hs x) (D.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((D.forward_openEmbedding s hs).injective (eq_of_heq h))

theorem M33RegularHistoryData.noncollapsed_ball
    {t r r0 kappa : ℝ} (ht : t ∈ H.generalized.interval)
    (z : (H.generalized.slice t).carrier)
    (hN : GeneralizedKappaNoncollapsedAt H.generalized ⟨t, z⟩ kappa r0)
    (hr : 0 < r) (hle : r ≤ r0)
    (e : SurgeryFlowCylinder F (F.slice t) t 1 (Icc (-r ^ 2) 0)
      ((F.metric t).ball (H.history.forward t ht z) r))
    (hbase : ∀ h y, y ∈ (F.metric t).ball (H.history.forward t ht z) r →
      HEq (e.forward 0 h y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric t).ball (H.history.forward t ht z) r →
      (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (F.metric t) ((F.metric t).ball (H.history.forward t ht z) r) := by
  let e' := e.restrict Ioc_subset_Icc_self ordConnected_Ioc (Subset.refl _)
  have htime := H.backward_time_subset ht e'
  obtain ⟨d, hd, _⟩ := H.cylinders_from_surgery (F.slice t) t 1 (Ioc (-r ^ 2) 0)
    ((F.metric t).ball (H.history.forward t ht z) r)
    (M04.initial_ball_isOpen _ _ _) htime e'
    (fun s hs => e'.regular_image_Ioc hs)
  let c := H.history.rebaseCylinder t ht z r d
  have hmaps (y : (H.generalized.slice t).carrier)
      (hy : y ∈ (H.generalized.metric t).ball z r) :
      H.history.forward t ht y ∈ (F.metric t).ball (H.history.forward t ht z) r :=
    H.history.ball_image_subset t ht z r ⟨y, hy, rfl⟩
  have hback : Ioc (t - r ^ 2) t ⊆ H.generalized.interval := by
    intro s hs
    have h := htime (s - t) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [div_one, add_sub_cancel] using h
  have hzero : ∀ h y, y ∈ (H.generalized.metric t).ball z r →
      c.pointMap 0 h y = (⟨t, y⟩ : H.generalized.point) := by
    intro h y hy
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply history_point_heq H.history (htime 0 h) ht (by simp)
    exact (heq_of_eq (hd 0 h _ (hmaps y hy))).trans
      (hbase (Ioc_subset_Icc_self h) _ (hmaps y hy))
  have hnorm : ∀ s hs y, y ∈ (H.generalized.metric t).ball z r →
      |H.generalized.curvatureNorm (c.pointMap s hs y)| ≤ r⁻¹ ^ 2 := by
    intro s hs y hy
    have hp := H.curvature_norm_pullback (t + s / 1) (htime s hs)
      (d.forward s hs (H.history.forward t ht y))
    rw [hd s hs _ (hmaps y hy)] at hp
    change |(H.generalized.connection (t + s / 1)).curvatureTensorNorm
      (d.forward s hs (H.history.forward t ht y))| ≤ r⁻¹ ^ 2
    rw [← hp, abs_of_nonneg (show 0 ≤ (F.connection (t + s / 1)).curvatureTensorNorm
      (e'.forward s hs (H.history.forward t ht y)) from Real.sqrt_nonneg _)]
    exact hcurv s (Ioc_subset_Icc_self hs) _ (hmaps y hy)
  have h := hN r hr hle hback c hzero hnorm
  rw [← H.volume_image t ht] at h
  exact h.trans (measure_mono (H.history.ball_image_subset t ht z r))

theorem M33RegularHistoryData.noncollapsedOn_of_generalized
    {J : Set ℝ} (hJ : J ⊆ H.generalized.interval) (kappa : ℝ)
    (hN : ∀ t ∈ J, ∀ ht : t ∈ H.generalized.interval,
      ∀ z : (H.generalized.slice t).carrier,
        ¬ SurgeryPositiveComponentAt F t (H.history.forward t ht z) →
          GeneralizedKappaNoncollapsedAt H.generalized ⟨t, z⟩ kappa F.parameters.epsilon) :
    SurgeryNoncollapsedOn F J kappa := by
  intro t ht _ x hpositive r hr hle e hbase hcurv
  have hterminal := e.terminal_ball_regular x hr hbase
  have hx : x ∈ (F.metric t).ball x r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal r
    simpa only [Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hr
  obtain ⟨z, hz⟩ : x ∈ range (H.history.forward t (hJ ht)) := by
    rw [H.regular_range]
    exact hterminal hx
  subst x
  exact H.noncollapsed_ball (hJ ht) z (hN t ht (hJ ht) z hpositive)
    hr hle e hbase hcurv

end PoincareConjecture
