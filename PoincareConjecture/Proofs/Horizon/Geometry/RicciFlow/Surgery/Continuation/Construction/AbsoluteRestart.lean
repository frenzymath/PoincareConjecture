import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.OrdinaryRestart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Surgery.OrdinaryRestart

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g₀ : RiemannianMetric n M}

theorem absolute_time_lt {a t : ℝ} (ha : 0 ≤ a) (ht : a ≤ t) :
    ENNReal.ofReal (t - a) < lifetime g₀ ↔
      ENNReal.ofReal t < ENNReal.ofReal a + lifetime g₀ := by
  have heq : ENNReal.ofReal t = ENNReal.ofReal a + ENNReal.ofReal (t - a) := by
    rw [← ENNReal.ofReal_add ha (sub_nonneg.mpr ht)]
    congr 1
    ring
  rw [heq, ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top]

noncomputable def absoluteFlow (hunique : RicciFlowUniqueness n M)
    (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a) :
    RicciFlow n M
      {t : ℝ | a ≤ t ∧ ENNReal.ofReal t < ENNReal.ofReal a + lifetime g₀} :=
  (maximalFlow hunique A).translate (-a)
    (by
      rintro s ⟨t, ht, rfl⟩
      exact ⟨by linarith [ht.1], by
        simpa only [sub_eq_add_neg] using (absolute_time_lt ha ht.1).mpr ht.2⟩)
    ⟨by
      intro s hs t ht r hr
      exact ⟨hs.1.trans hr.1, (ENNReal.ofReal_le_ofReal hr.2).trans_lt ht.2⟩⟩
    (by
      have hstart : ENNReal.ofReal a < ENNReal.ofReal a + lifetime g₀ := by
        simpa only [sub_self, ENNReal.ofReal_zero] using
          (absolute_time_lt ha (le_refl a)).mp (by
            simpa only [sub_self, ENNReal.ofReal_zero] using lifetime_pos A)
      refine ⟨a, ⟨le_rfl, hstart⟩, a + A.time / 2,
        ⟨by linarith [A.time_pos], ?_⟩, ?_⟩
      · apply (absolute_time_lt ha (by linarith [A.time_pos])).mp
        rw [add_sub_cancel_left]
        exact solution_time_lt A (by linarith [A.time_pos])
      · linarith [A.time_pos])

theorem absoluteFlow_initial (hunique : RicciFlowUniqueness n M)
    (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a) :
    (absoluteFlow hunique A a ha).metric a = g₀ := by
  change (maximalFlow hunique A).metric (a + -a) = g₀
  rw [add_neg_cancel]
  exact maximalFlow_initial hunique A

theorem absolute_lifetime_gt (A : Solution g₀) (a : ℝ) :
    ENNReal.ofReal a < ENNReal.ofReal a + lifetime g₀ := by
  simpa only [add_zero] using
    (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mpr (lifetime_pos A)

theorem absolute_time_le_lifetime {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow n M (Ico a b)) (hinitial : F.metric a = g₀) :
    ENNReal.ofReal b ≤ ENNReal.ofReal a + lifetime g₀ := by
  let B : Solution g₀ := {
    time := b - a
    time_pos := sub_pos.mpr hab
    flow := F.translate a
      (K := Ico 0 (b - a))
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ordConnected_Ico
      ⟨0, ⟨le_rfl, by linarith⟩, (b - a) / 2,
        ⟨by linarith, by linarith⟩, by linarith⟩
    initial := by
      change F.metric (0 + a) = g₀
      simpa only [zero_add] using hinitial }
  have heq : ENNReal.ofReal b = ENNReal.ofReal a + ENNReal.ofReal (b - a) := by
    rw [← ENNReal.ofReal_add ha (sub_nonneg.mpr hab.le)]
    congr 1
    ring
  rw [heq]
  exact add_le_add le_rfl (time_le_lifetime B)

theorem finite_absolute_domain (a : ℝ) (ha : 0 ≤ a)
    (hfinite : ENNReal.ofReal a + lifetime g₀ ≠ ⊤) :
    {t : ℝ | a ≤ t ∧ ENNReal.ofReal t < ENNReal.ofReal a + lifetime g₀} =
      Ico a (ENNReal.ofReal a + lifetime g₀).toReal := by
  ext t
  constructor
  · rintro ⟨ht, he⟩
    exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal (ha.trans ht) hfinite).mp he⟩
  · rintro ⟨ht, he⟩
    exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal (ha.trans ht) hfinite).mpr he⟩

noncomputable def finiteAbsoluteFlow (hunique : RicciFlowUniqueness n M)
    (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a)
    (hfinite : ENNReal.ofReal a + lifetime g₀ ≠ ⊤) :
    RicciFlow n M (Ico a (ENNReal.ofReal a + lifetime g₀).toReal) where
  metric := (absoluteFlow hunique A a ha).metric
  connection := (absoluteFlow hunique A a ha).connection
  interval := ordConnected_Ico
  nontrivial := by
    rw [← finite_absolute_domain a ha hfinite]
    exact (absoluteFlow hunique A a ha).nontrivial
  smooth := by
    rw [← finite_absolute_domain a ha hfinite]
    exact (absoluteFlow hunique A a ha).smooth
  equation := by
    rw [← finite_absolute_domain a ha hfinite]
    exact (absoluteFlow hunique A a ha).equation

theorem absolute_curvature_unbounded_tail [CompactSpace M]
    (hlocal : RicciFlowLocalTheory n M) (A : Solution g₀) (a : ℝ) (ha : 0 ≤ a)
    (hfinite : ENNReal.ofReal a + lifetime g₀ ≠ ⊤)
    (C s : ℝ) (hs : s < (ENNReal.ofReal a + lifetime g₀).toReal) :
    ∃ t ∈ Ioo (max a s) (ENNReal.ofReal a + lifetime g₀).toReal, ∃ x : M,
      C < ((absoluteFlow hlocal.2.1 A a ha).connection t).curvatureTensorNorm x := by
  have hL : lifetime g₀ ≠ ⊤ := by
    intro h
    exact hfinite (by rw [h, add_top])
  have hend : (ENNReal.ofReal a + lifetime g₀).toReal = a + (lifetime g₀).toReal := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hL, ENNReal.toReal_ofReal ha]
  obtain ⟨t, ht, x, hx⟩ := finite_curvature_unbounded_tail hlocal A hL C (s - a)
    (by rw [hend] at hs; linarith)
  refine ⟨a + t, ⟨?_, ?_⟩, x, ?_⟩
  · have ht0 := (le_max_left 0 (s - a)).trans_lt ht.1
    have hts := (le_max_right 0 (s - a)).trans_lt ht.1
    exact max_lt (by linarith) (by linarith)
  · rw [hend]
    linarith [ht.2]
  · change C < ((maximalFlow hlocal.2.1 A).connection ((a + t) + -a)).curvatureTensorNorm x
    rw [show (a + t) + -a = t by ring]
    exact hx

end PoincareConjecture.Surgery.OrdinaryRestart
