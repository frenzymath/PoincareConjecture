import PoincareConjecture.Proofs.M76.Mathlib.RaisingCutHeightSigns
import Mathlib.Topology.Instances.Real.Lemmas










set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]





theorem mem_both_height_closures_of_fixed_negative_cut
    {S s s' d : Set E} (H : E ≃ₜ E) (A : E → ℝ) (hA : Continuous A)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {y | A y = 0})
    (hfix : ∀ y ∈ s, A y < 0 → H y = y)
    {x : E} (hxs : x ∈ s) (hxA : A x < 0)
    (hlo : x ∈ closure (S ∩ {y | A y < A x}))
    (hhi : x ∈ closure (S ∩ {y | A x < A y})) :
    x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hxnot : x ∉ s' := fun hx => hxA.ne (hcut ⟨hxs, hx⟩)
  let U := {y | A y < 0} ∩ s'ᶜ
  have hU : IsOpen U := (isOpen_lt hA continuous_const).inter hs'.isOpen_compl
  have hxU : x ∈ U := ⟨hxA, hxnot⟩
  have hlocal {V : Set E} (hx : x ∈ closure (S ∩ V)) :
      x ∈ closure ((H '' (s ∪ d)) ∩ V) := by
    apply closure_mono _ (hU.inter_closure ⟨hxU, hx⟩)
    intro y hy
    have hys : y ∈ s := (hunion.symm.subset hy.2.1).resolve_right hy.1.2
    exact ⟨⟨y, Or.inl hys, hfix y hys hy.1.1⟩, hy.2.2⟩
  exact ⟨hlocal hlo, hlocal hhi⟩

end Homeomorph
