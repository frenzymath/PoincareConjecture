import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousOn
import Mathlib.Logic.Equiv.Basic










set_option autoImplicit false

open Set

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X] {S : Set X}

private theorem continuous_closedExtension (e : S ≃ₜ S) (hS : IsClosed S)
    (he : ∀ x : S, (x : X) ∈ frontier S → e x = x) :
    letI := Classical.propDecidable
    Continuous (Equiv.Perm.extendDomain e.toEquiv (Equiv.refl S) : X → X) := by
  classical
  let f : X → X := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl S)
  have hfS : ContinuousOn f S := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    ext x
    exact Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl S) x.property
  have hfix : EqOn f id (closure Sᶜ) := by
    intro x hx
    by_cases hxS : x ∈ S
    · have hfront : x ∈ frontier S := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hxS, hx⟩
      simpa [f, Equiv.Perm.extendDomain_apply_subtype _ _ hxS] using
        congrArg Subtype.val (he ⟨x, hxS⟩ hfront)
    · exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hxS
  have hcover : S ∪ closure Sᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ S
    · exact Or.inl hx
    · exact Or.inr (subset_closure hx)
  have hcont := hfS.union_of_isClosed (continuous_id.continuousOn.congr hfix)
    hS isClosed_closure
  rw [hcover] at hcont
  exact continuousOn_univ.mp hcont



noncomputable def closedExtension (e : S ≃ₜ S) (hS : IsClosed S)
    (he : ∀ x : S, (x : X) ∈ frontier S → e x = x) : X ≃ₜ X := by
  classical
  refine
    { toEquiv := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl S)
      continuous_toFun := continuous_closedExtension e hS he
      continuous_invFun := continuous_closedExtension e.symm hS ?_ }
  intro x hx
  apply e.injective
  rw [e.apply_symm_apply, he x hx]



theorem closedExtension_apply_mem (e : S ≃ₜ S) (hS : IsClosed S)
    (he : ∀ x : S, (x : X) ∈ frontier S → e x = x) {x : X} (hx : x ∈ S) :
    e.closedExtension hS he x = (e ⟨x, hx⟩ : X) := by
  classical
  exact Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl S) hx



theorem closedExtension_apply_notMem (e : S ≃ₜ S) (hS : IsClosed S)
    (he : ∀ x : S, (x : X) ∈ frontier S → e x = x) {x : X} (hx : x ∉ S) :
    e.closedExtension hS he x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hx



theorem closedExtension_apply_frontier (e : S ≃ₜ S) (hS : IsClosed S)
    (he : ∀ x : S, (x : X) ∈ frontier S → e x = x) {x : X} (hx : x ∈ frontier S) :
    e.closedExtension hS he x = x := by
  rw [e.closedExtension_apply_mem hS he (hS.frontier_subset hx)]
  exact congrArg Subtype.val (he _ hx)

end Homeomorph
