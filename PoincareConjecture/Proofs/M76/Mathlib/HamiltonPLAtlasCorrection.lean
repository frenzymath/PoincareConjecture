import PoincareConjecture.Proofs.M76.Mathlib.ExtendByIdentity
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set

namespace Function.Injective

variable {X : Type*} {f : X → X}

theorem preimage_eq_self_of_eqOn_compl (hf : Injective f) {U : Set X}
    (hfix : EqOn f id Uᶜ) : f ⁻¹' U = U := by
  ext x
  change f x ∈ U ↔ x ∈ U
  by_cases hx : x ∈ U
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    by_contra hfx
    have heq : f x = x := hf (hfix hfx)
    exact hfx (heq.symm ▸ hx)
  · rw [hfix hx]
    rfl

end Function.Injective

namespace OpenPartialHomeomorph

variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]

theorem exists_supported_overlap_chart_correction
    (c : OpenPartialHomeomorph M E) {U K : Set M}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U ∩ c.source)
    (h : (U ∩ c.source : Set M) ≃ₜ (U ∩ c.source : Set M))
    (hfix : ∀ x : (U ∩ c.source : Set M), (x : M) ∉ K → h x = x) :
    ∃ H : M ≃ₜ M,
      (∀ x : (U ∩ c.source : Set M), H x = (h x : M)) ∧
      EqOn (H : M → M) id Kᶜ ∧ H ⁻¹' U = U ∧
      (H.transOpenPartialHomeomorph c).source = c.source ∧
      (H.transOpenPartialHomeomorph c).target = c.target ∧
      (∀ x : (U ∩ c.source : Set M),
        H.transOpenPartialHomeomorph c x = c (h x)) ∧
      EqOn (H.transOpenPartialHomeomorph c : M → E) c Kᶜ := by
  let H := h.extendByIdentity (hU.inter c.open_source) hK hKU hfix
  have hlocal (x : (U ∩ c.source : Set M)) : H x = (h x : M) :=
    h.extendByIdentity_apply_mem (hU.inter c.open_source) hK hKU hfix x.property
  have hfixed : EqOn (H : M → M) id Kᶜ := fun _ hx =>
    h.extendByIdentity_apply_of_notMem (hU.inter c.open_source) hK hKU hfix hx
  have hpresU : H ⁻¹' U = U := H.injective.preimage_eq_self_of_eqOn_compl
    (fun _ hx => hfixed (fun hxK => hx (hKU hxK).1))
  have hpresV : H ⁻¹' c.source = c.source := H.injective.preimage_eq_self_of_eqOn_compl
    (fun _ hx => hfixed (fun hxK => hx (hKU hxK).2))
  refine ⟨H, hlocal, hfixed, hpresU, hpresV, rfl, ?_, ?_⟩
  · intro x
    change c (H x) = c (h x)
    rw [hlocal]
  · intro x hx
    change c (H x) = c x
    rw [hfixed hx]
    rfl

end OpenPartialHomeomorph
