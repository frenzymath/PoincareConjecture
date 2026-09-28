import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.RadialDistance
import Mathlib.Topology.Sequences











set_option autoImplicit false

open Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M34



theorem capRiemannianMetric_complete {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) : MetricComplete (capRiemannianMetric a ha hapi) := by
  have hc (R : ℝ) : IsCompact {x : StandardCapSpace | ‖x‖ ≤ R} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : StandardCapSpace) R
  let g := capRiemannianMetric a ha hapi
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle StandardCapSpace
      (TangentSpace (𝓡 3) : StandardCapSpace → Type) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace StandardCapSpace := EMetricSpace.ofRiemannianMetric (𝓡 3) StandardCapSpace
  let : PseudoEMetricSpace StandardCapSpace :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) StandardCapSpace).toPseudoEMetricSpace
  let : UniformSpace StandardCapSpace :=
    (EMetricSpace.ofRiemannianMetric (𝓡 3) StandardCapSpace).toUniformSpace
  change CompleteSpace StandardCapSpace
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  have hbound : ∀ n ≥ N, ‖u n‖ ≤ ‖u N‖ + 1 := by
    intro n hn
    have hd : g.edist (u N) (u n) ≤ 1 := by
      have h := (hN n hn).le
      change g.edist (u n) (u N) ≤ 1 at h
      exact (show g.edist (u N) (u n) = g.edist (u n) (u N) from
        riemannianEDist_comm).le.trans h
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ‖u N‖ + 1)).mp
    calc
      ENNReal.ofReal ‖u n‖ = g.edist 0 (u n) :=
        (capRiemannianMetric_edist_zero ha hapi (u n)).symm
      _ ≤ g.edist 0 (u N) + g.edist (u N) (u n) := riemannianEDist_triangle
      _ ≤ ENNReal.ofReal ‖u N‖ + 1 := by
        rw [show g.edist 0 (u N) = ENNReal.ofReal ‖u N‖ from
          capRiemannianMetric_edist_zero ha hapi (u N)]
        exact add_le_add le_rfl hd
      _ = ENNReal.ofReal (‖u N‖ + 1) := by
        rw [ENNReal.ofReal_add (norm_nonneg _) zero_le_one, ENNReal.ofReal_one]
  obtain ⟨p, _, φ, hφ, hp⟩ := (hc (‖u N‖ + 1)).tendsto_subseq'
    (Filter.Eventually.frequently (Filter.eventually_atTop.mpr ⟨N, hbound⟩))
  exact ⟨p, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hp⟩

end PoincareConjecture.M34
