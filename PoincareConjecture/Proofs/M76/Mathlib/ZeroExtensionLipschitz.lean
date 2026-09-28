import PoincareConjecture.Proofs.M76.Mathlib.FiniteClosedCoverLipschitz
import Mathlib.Topology.Algebra.Indicator









set_option autoImplicit false

open Set
open scoped NNReal





theorem LipschitzOnWith.indicator_of_eq_zero_frontier {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {s : Set E} {f : E → F} {L : ℝ≥0} (hf : LipschitzOnWith L f s)
    (hs : IsClosed s) (hzero : ∀ x ∈ frontier s, f x = 0) :
    LipschitzWith L (s.indicator f) := by
  classical
  have hc : Continuous (s.indicator f) := continuous_indicator hzero (by
    rw [hs.closure_eq]
    exact hf.continuousOn)
  have hfix : EqOn (s.indicator f) (fun _ => 0) (closure sᶜ) := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs, hzero x]
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hxs, hx⟩
    · exact indicator_of_notMem hxs f
  apply lipschitzOnWith_univ.mp
  apply convex_univ.lipschitzOnWith_of_finite_closed_cover hc.continuousOn
    (fun i : Bool => if i then s else closure sᶜ) ?_ ?_ ?_
  · intro i
    cases i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact isClosed_closure
    · exact hs
  · intro x _
    by_cases hx : x ∈ s
    · exact mem_iUnion.mpr ⟨true, hx⟩
    · exact mem_iUnion.mpr ⟨false, subset_closure hx⟩
  · intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    cases i
    · rw [hfix hx.2, hfix hy.2, dist_self]
      exact mul_nonneg L.coe_nonneg dist_nonneg
    · rw [indicator_of_mem (show x ∈ s from hx.2), indicator_of_mem (show y ∈ s from hy.2)]
      exact hf.dist_le_mul x hx.2 y hy.2
