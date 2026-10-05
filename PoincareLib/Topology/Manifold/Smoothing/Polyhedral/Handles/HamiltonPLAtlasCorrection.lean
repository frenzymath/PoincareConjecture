import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ExtendByIdentity
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Supported correction of an incoming chart

A self-homeomorphism of an overlap, supported in a closed subset
of that overlap, extends by the identity and preserves both open
regions. Precomposing the incoming chart keeps its exact source
and target. See Hamilton 1976, Theorem 2.1, p. 69 and
M76 derivation 258.
-/

set_option autoImplicit false

open Set

namespace Function.Injective

variable {X : Type*} {f : X → X}

/-- An injective map fixing the complement of a set preserves
that set exactly. A moved point cannot map to a fixed exterior
point. See Hamilton p. 69 and M76 derivation 258. -/
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

/-- Extending the actual supported overlap correction gives
an ambient map preserving the old region and the incoming
chart source. The corrected chart agrees literally with the
local correction on the overlap and with the old chart off
the support. No PL straightening is asserted here.
See Hamilton p. 69 and M76 derivation 258. -/
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
