import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Real.Basic

/-!
# Upper height signs at fixed points of a raised cut

The closed opposite cut is absent near a positive-height point.
Its original upper approach consequently lies in the chosen cut
and stays above the fixed point under a height-raising map.
See Alexander 1924, pp. 7--8 and M76 derivation 256.
-/

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

/-- A fixed positive-height cut point keeps its original upper
approach under the same height-raising homeomorphism. The cuts
meet only at zero, so closedness of the opposite cut localizes
the original approach. See Alexander pp. 7--8 and derivation 256. -/
theorem mem_upper_height_closure_of_raising_cut
    {S s s' d : Set E} (H : E ≃ₜ E) (A : E → ℝ)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {y | A y = 0})
    (hraise : ∀ y ∈ s, A y ≤ A (H y))
    {x : E} (hxs : x ∈ s) (hxA : 0 < A x) (hfix : H x = x)
    (hsource : x ∈ closure (S ∩ {y | A x < A y})) :
    x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hxnot : x ∉ s' := fun hx => hxA.ne' (hcut ⟨hxs, hx⟩)
  have hlocal : x ∈ closure (s ∩ {y | A x < A y}) := by
    apply closure_mono _ (hs'.isOpen_compl.inter_closure ⟨hxnot, hsource⟩)
    intro y hy
    exact ⟨(hunion.symm.subset hy.2.1).resolve_right hy.1, hy.2.2⟩
  have hmap : MapsTo H (s ∩ {y | A x < A y})
      ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
    intro y hy
    exact ⟨⟨y, Or.inl hy.1, rfl⟩, hy.2.trans_le (hraise y hy.1)⟩
  have h := H.continuous.continuousWithinAt.mem_closure hlocal hmap
  rwa [hfix] at h

end Homeomorph
