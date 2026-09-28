import PoincareConjecture.Proofs.M32.Mathlib.CommonAvoidance
import PoincareConjecture.Definitions.Ch11.SingularLimits
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

section Single

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem singularTimeAssumptions_singularTimes_countable
    (H : SingularTimeAssumptions F T M) : H.singularTimes.Countable := by
  have hdiscrete : IsDiscrete H.singularTimes := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro s hs
    obtain ⟨delta, hdelta, hsep⟩ := H.singularTimes_discrete s hs
    refine ⟨Metric.ball s delta, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨ht, hts⟩
      apply mem_singleton_iff.mpr
      by_contra hne
      have hlt : |t - s| < delta := by
        simpa only [Metric.mem_ball, Real.dist_eq] using ht
      exact (not_le_of_gt hlt) (hsep t hts hne)
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  exact (HereditarilyLindelofSpace.isLindelof H.singularTimes).countable_of_isDiscrete
    hdiscrete

end Single

section Sequence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}

theorem exists_common_regular_normalized_time
    (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
    (q : ℕ → ℝ) (hq : ∀ k, 0 < q k) {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, t ∈ Ioo a b ∧ ∀ k, T k + t / q k ∉ (H k).singularTimes := by
  apply exists_between_avoiding_countable_preimages
    (fun k => (H k).singularTimes)
    (fun k => singularTimeAssumptions_singularTimes_countable (H k))
    (fun k t => T k + t / q k) _ hab
  intro k s t h
  exact (div_left_inj' (hq k).ne').mp (add_left_cancel h)

end Sequence

end PoincareConjecture.M32
