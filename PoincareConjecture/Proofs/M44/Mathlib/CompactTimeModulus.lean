import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

theorem ContinuousOn.exists_uniform_time_delta
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {I : Set ℝ} {K : Set X} {f : ℝ × X → Y}
    (hf : ContinuousOn f (I ×ˢ K)) (hI : IsCompact I) (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ I, ∀ t ∈ I, |s - t| < delta →
      ∀ x ∈ K, dist (f (s, x)) (f (t, x)) < epsilon := by
  obtain ⟨delta, hdelta, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((hI.prod hK).uniformContinuousOn_of_continuous hf) epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst x hx
  apply hmod (s, x) ⟨hs, hx⟩ (t, x) ⟨ht, hx⟩
  simpa only [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg (s - t))]
    using hst
