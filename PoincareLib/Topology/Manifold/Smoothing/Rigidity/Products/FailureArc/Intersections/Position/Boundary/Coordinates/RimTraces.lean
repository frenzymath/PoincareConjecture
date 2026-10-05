import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Real.Basic

/-! # Exact whole lower-rim traces in the common boundary collar -/

set_option autoImplicit false
open Set

namespace PoincareMT.M76

theorem common_collar_zero_trace_inter_component
    {E Z X C : Type*} [TopologicalSpace Z] [TopologicalSpace C]
    {Q : Set Z} {S₀ S₁ : Set X} (hdis : Disjoint S₀ S₁)
    (c : E × ℝ → X) (rim : Bool → Z → E) (f : Bool → Z → X)
    (hbase : ∀ b z, z ∈ Q → c (rim b z, 0) = f b z)
    (k : C → X) (q : Q ≃ₜ C)
    (hlower : ∀ z : Q, f false z = k (q z))
    (hk : range k ⊆ S₀) (hupper : MapsTo (f true) Q S₁) :
    (c '' (((rim false '' Q) ∪ (rim true '' Q)) ×ˢ ({0} : Set ℝ))) ∩ S₀ = range k := by
  ext x
  constructor
  · rintro ⟨⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩, hx⟩
    have ht0 : t = 0 := ht
    subst t
    rcases hz with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact ⟨q ⟨z, hz⟩, (hlower ⟨z, hz⟩).symm.trans (hbase false z hz).symm⟩
    · exact False.elim ((Set.disjoint_left.mp hdis) hx
        ((hbase true z hz).symm ▸ hupper hz))
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := q.surjective x
    refine ⟨⟨(rim false z, 0), ⟨Or.inl ⟨z, z.property, rfl⟩, rfl⟩, ?_⟩, hk ⟨x, rfl⟩⟩
    exact (hbase false z z.property).trans ((hlower z).trans (congrArg k hz))

end PoincareMT.M76
