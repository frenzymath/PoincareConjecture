import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousOn
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

open Set

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X] {U K : Set X}

theorem symm_eqOn_compl (e : U ≃ₜ U)
    (he : ∀ x : U, (x : X) ∉ K → e x = x) :
    ∀ x : U, (x : X) ∉ K → e.symm x = x := by
  intro x hx
  apply e.injective
  rw [e.apply_symm_apply, he x hx]

private theorem continuous_extendDomain (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (he : ∀ x : U, (x : X) ∉ K → e x = x) :
    letI := Classical.propDecidable
    Continuous (Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U) : X → X) := by
  classical
  let f : X → X := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U)
  have hfU : ContinuousOn f U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    ext x
    exact Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl U) x.property
  have hfK : EqOn f id Kᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · simpa [f, Equiv.Perm.extendDomain_apply_subtype _ _ hxU] using
        congrArg Subtype.val (he ⟨x, hxU⟩ hx)
    · simp [f, Equiv.Perm.extendDomain_apply_not_subtype _ _ hxU]
  have hcover : U ∪ Kᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  have hf := hfU.union_of_isOpen (continuous_id.continuousOn.congr hfK) hU hK.isOpen_compl
  rw [hcover] at hf
  exact continuousOn_univ.mp hf

noncomputable def extendByIdentity (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (he : ∀ x : U, (x : X) ∉ K → e x = x) : X ≃ₜ X := by
  classical
  exact
    { toEquiv := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U)
      continuous_toFun := continuous_extendDomain e hU hK hKU he
      continuous_invFun := continuous_extendDomain e.symm hU hK hKU (e.symm_eqOn_compl he) }

theorem extendByIdentity_apply_mem (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (he : ∀ x : U, (x : X) ∉ K → e x = x) {x : X} (hx : x ∈ U) :
    e.extendByIdentity hU hK hKU he x = (e ⟨x, hx⟩ : X) := by
  classical
  exact Equiv.Perm.extendDomain_apply_subtype _ _ hx

theorem extendByIdentity_apply_of_notMem (e : U ≃ₜ U) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U)
    (he : ∀ x : U, (x : X) ∉ K → e x = x) {x : X} (hx : x ∉ K) :
    e.extendByIdentity hU hK hKU he x = x := by
  classical
  by_cases hxU : x ∈ U
  · rw [e.extendByIdentity_apply_mem hU hK hKU he hxU]
    exact congrArg Subtype.val (he ⟨x, hxU⟩ hx)
  · exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hxU

end Homeomorph
