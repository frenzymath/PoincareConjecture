import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Poincare

theorem exists_height_tail_disjoint_compact
    {M : Type*} [TopologicalSpace M] {U P : Set M} (h : U → ℝ)
    (hh : Continuous h) (hupper : ∀ x, h x < 1)
    (hclosure : closure P ⊆ U) (hside : ∀ x : U, (1 / 2 : ℝ) < h x → x.val ∈ P)
    {K : Set M} (hK : IsCompact K) :
    ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧ ∀ x : U, a < h x → x.val ∉ K := by
  let C : Set U := (Subtype.val : U → M) ⁻¹' (K ∩ closure P)
  have hC : IsCompact C :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (hK.inter_right isClosed_closure) (by
        intro x hx
        exact ⟨⟨x, hclosure hx.2⟩, rfl⟩)
  obtain ⟨m, hm, hbound⟩ := hC.exists_forall_le'
    (continuous_const.sub hh).continuousOn (fun x _ => sub_pos.mpr (hupper x))
  obtain ⟨a, ha, ha1⟩ := exists_between
    (max_lt (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : 1 - m < 1))
  refine ⟨a, (le_max_left _ _).trans_lt ha, ha1, ?_⟩
  intro x hx hxK
  have hxP := hside x (((le_max_left _ _).trans_lt ha).trans hx)
  have hlow := hbound x ⟨hxK, subset_closure hxP⟩
  change m ≤ 1 - h x at hlow
  have hhigh := (le_max_right (1 / 2 : ℝ) (1 - m)).trans_lt ha
  linarith

end Poincare
