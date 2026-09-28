import PoincareConjecture.Proofs.M76.Mathlib.VanishingDisplacementExtension
import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] {U : Set E}

theorem exists_extension_of_compact_vanishing_bound (e : U ≃ₜ U)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    {b : E → ℝ} (hb : Continuous b) (hbzero : EqOn b (fun _ => 0) Uᶜ)
    (hbound : ∀ x : U, ‖(e x : E) - x‖ ≤ b x) :
    ∃ F : E ≃ₜ E,
      (∀ x : U, F x = (e x : E)) ∧ ∀ x ∉ U, F x = x := by
  classical
  let f : E ≃ E := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U)
  have hfU (x : E) (hx : x ∈ U) : f x = (e ⟨x, hx⟩ : E) :=
    Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl U) hx
  have hfix (x : E) (hx : x ∉ U) : f x = x :=
    Equiv.Perm.extendDomain_apply_not_subtype e.toEquiv (Equiv.refl U) hx
  have hcont : Continuous f := e.continuous_extendDomain_of_vanishing_bound hU hb hbzero hbound
  have hmem (x : E) : x ∈ closure U ↔ f x ∈ closure U := by
    by_cases hx : x ∈ U
    · exact iff_of_true (subset_closure hx)
        (by rw [hfU x hx]; exact subset_closure (e ⟨x, hx⟩).property)
    · rw [hfix x hx]
  let fc : closure U ≃ closure U := f.subtypeEquiv hmem
  let : CompactSpace (closure U) := isCompact_iff_compactSpace.mp hcompact
  let ec : closure U ≃ₜ closure U :=
    (hcont.comp continuous_subtype_val |>.subtype_mk _).homeoOfEquivCompactToT2 (f := fc)
  have hec (x : closure U) : (ec x : E) = f x := rfl
  have hfront (x : closure U) (hx : (x : E) ∈ frontier (closure U)) : ec x = x := by
    apply Subtype.ext
    rw [hec]
    apply hfix
    intro hxU
    have hnot := (frontier_closure_subset hx).2
    exact hnot (hU.interior_eq.symm ▸ hxU)
  let F := ec.closedExtension isClosed_closure hfront
  refine ⟨F, ?_, ?_⟩
  · intro x
    rw [closedExtension_apply_mem _ _ _ (subset_closure x.property), hec, hfU _ x.property]
  · intro x hx
    by_cases hc : x ∈ closure U
    · rw [closedExtension_apply_mem _ _ _ hc, hec, hfix x hx]
    · exact ec.closedExtension_apply_notMem isClosed_closure hfront hc

end Homeomorph
