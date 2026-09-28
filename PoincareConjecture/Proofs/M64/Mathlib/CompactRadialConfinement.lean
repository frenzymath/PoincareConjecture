import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.ProperSpace









set_option autoImplicit false

open Set Metric
open scoped Topology

namespace PoincareConjecture




theorem m64_isCompact_confined_radial_vectors
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [TopologicalSpace X] {e : E → X} {R : ℝ}
    (he : ContinuousOn e (closedBall 0 R)) {B : Set X} (hB : IsClosed B) :
    IsCompact {v : E | ‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ B} := by
  have hclosed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      IsClosed (closedBall (0 : E) R ∩ (fun v => e (t • v)) ⁻¹' B) := by
    have hmap : MapsTo (fun v : E => t • v) (closedBall 0 R) (closedBall 0 R) := by
      intro v hv
      rw [mem_closedBall, dist_zero_right] at hv ⊢
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans (by simpa using hv)
    have hc := he.comp (continuous_const.smul continuous_id).continuousOn hmap
    exact hc.preimage_isClosed_of_isClosed isClosed_closedBall hB
  have heq : {v : E | ‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ B} =
      ⋂ t ∈ Icc (0 : ℝ) 1, closedBall 0 R ∩ (fun v : E => e (t • v)) ⁻¹' B := by
    ext v
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage,
      mem_closedBall, dist_zero_right]
    constructor
    · intro hv t ht
      exact ⟨hv.1, hv.2 t ht⟩
    · intro hv
      exact ⟨(hv 0 ⟨le_rfl, zero_le_one⟩).1, fun t ht => (hv t ht).2⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset
  · rw [heq]
    exact isClosed_biInter hclosed
  · intro v hv
    simpa only [mem_closedBall, dist_zero_right] using hv.1

end PoincareConjecture
