import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsNativeFamily
import PoincareConjecture.Proofs.M35.RadialGauge.NativeDeTurckEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge DeTurckNative

theorem exists_raw_corrected_deturck_metric
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Ico 0 T) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ T - t₀ ∧
      ∃ (w : ℝ → ℝ → ℝ)
        (Φ : ℝ → Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞),
        w 0 = 0 ∧
        (∀ t ∈ Icc 0 delta, ∀ x, Φ t x = rawIntrinsicGaugeMap G t₀ w t x) ∧
        (∀ x, Φ 0 x = intrinsicSpatialCoordinate (G.flow.metric t₀) x) ∧
        gaugePullbackMetric (G.flow.metric t₀) (Φ 0).symm =
          intrinsicSpatialMetric (G.flow.metric t₀)
            (hrotation t₀ ⟨ht₀.1, ht₀.2.trans hTlt⟩)
            (G.complete P ⟨ht₀.1, ht₀.2.trans hTlt⟩) ∧
        (∀ t ∈ Icc 0 delta, ∀ r,
          1 / 2 ≤ deriv (mapRadius (w t)) r ∧ |mapRadius (w t) r - r| ≤ 1 / 4) ∧
        (∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ t ∈ Icc 0 delta, ∀ r,
          (1 + |r|) * |deriv (deriv (w t)) r| ≤ C ∧
          (1 + |r|) * |deriv (deriv (deriv (w t))) r| ≤ D) ∧
        (∀ epsilon > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 delta, ∀ r, R ≤ |r| →
          (1 + |r|) * |deriv (w t) r| < epsilon ∧
          (1 + |r|) * |deriv (deriv (w t)) r| < epsilon) ∧
        ContDiffOn ℝ 2 (fun p : ℝ × StandardCapSpace => Φ p.1 p.2)
          (Ioo 0 delta ×ˢ univ) ∧
        ContDiffOn ℝ 2 (fun p : ℝ × StandardCapSpace => (Φ p.1).symm p.2)
          (Ioo 0 delta ×ˢ univ) ∧
        ∀ B : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric t₀)
            (hrotation t₀ ⟨ht₀.1, ht₀.2.trans hTlt⟩)
            (G.complete P ⟨ht₀.1, ht₀.2.trans hTlt⟩)),
          ∀ t ∈ Ioo 0 delta,
          ∀ K : LeviCivitaData (gaugePullbackMetric (G.flow.metric (t₀ + t)) (Φ t).symm),
          (∀ x, HasDerivAt (fun a => Φ a x) (-intrinsicDeTurckField K B (Φ t x)) t) ∧
          ∀ x u v, HasDerivAt
            (fun a => (gaugePullbackMetric (G.flow.metric (t₀ + a)) (Φ a).symm).inner x u v)
            (-2 * K.ricci x u v + metricLieDerivative K (intrinsicDeTurckField K B) x u v) t := by
  obtain ⟨delta, hd, hdT, w, Φ, hw0, hmap, hzero, hr, h23, hend, hc, hv⟩ :=
    exists_raw_native_deturck_gauge P H G hrotation hT hTlt ht₀
  refine ⟨delta, hd, hdT, w, Φ, hw0, hmap, hzero, ?_, hr, h23, hend, hc, ?_, ?_⟩
  · have hinitial : Φ 0 = intrinsicSpatialDiffeomorph (G.flow.metric t₀)
        (hrotation t₀ ⟨ht₀.1, ht₀.2.trans hTlt⟩)
        (G.complete P ⟨ht₀.1, ht₀.2.trans hTlt⟩) := by
      apply Diffeomorph.ext
      intro x
      exact hzero x
    rw [hinitial]
    rfl
  · intro p hp
    exact (diffeomorph_family_symm_contDiffAt_order (k := 2) (by norm_num)
      isOpen_Ioo hc hp.1).contDiffWithinAt
  · intro B t ht K
    refine ⟨hv B t ht K, ?_⟩
    intro x u v
    have htG : t₀ + t ∈ Ioo 0 G.lifetime := by
      refine ⟨add_pos_of_nonneg_of_pos ht₀.1 ht.1, lt_of_le_of_lt ?_ hTlt⟩
      linarith only [ht.2, hdT]
    exact inverse_pullback_solves_native_deturck G.flow isOpen_Ioo hc ht
      (Ico_mem_nhds htG.1 htG.2) B K (hv B t ht K) x u v

end PoincareConjecture.M35.Uniqueness
