import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Exact edge incidence from height-preserving lateral paths

When height is injective on an edge and a collar's corresponding
lateral path lies on that edge, injectivity of the collar gives
membership in both directions. See Alexander 1924, pp. 6--8
and M76 derivation 163.
-/

set_option autoImplicit false

open Set

namespace Homeomorph

/-- A height-preserving product homeomorphism with a specified
edge path preserves membership in that edge exactly. The base
height is constant and height is injective on the edge.
See M76 derivation 163. -/
theorem edge_membership_iff {E : Type*} [TopologicalSpace E]
    {B S C : Set E} {I : Set ℝ} (H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ S)
    (A : E → ℝ) {α : ℝ} (hbase : ∀ x ∈ B, A x = α)
    (hheight : ∀ p, A (H p) = (p : E × ℝ).2) (hC : InjOn A C)
    {l : E} (hlB : l ∈ B) (hlC : l ∈ C)
    (hpath : ∀ (t : ℝ) (ht : t ∈ I), (H ⟨(l, t), ⟨hlB, ht⟩⟩ : E) ∈ C)
    (p : (B ×ˢ I : Set (E × ℝ))) : (p : E × ℝ).1 ∈ C ↔ (H p : E) ∈ C := by
  let q : (B ×ˢ I : Set (E × ℝ)) := ⟨(l, (p : E × ℝ).2), ⟨hlB, p.property.2⟩⟩
  constructor
  · intro hpC
    have hpl : (p : E × ℝ).1 = l := hC hpC hlC
      ((hbase _ p.property.1).trans (hbase l hlB).symm)
    have hpq : p = q := Subtype.ext (Prod.ext hpl rfl)
    rw [hpq]
    exact hpath _ p.property.2
  · intro hpC
    have hH : H p = H q := Subtype.ext (hC hpC (hpath _ p.property.2)
      ((hheight p).trans (hheight q).symm))
    have hpl : (p : E × ℝ).1 = l :=
      congrArg (fun z : (B ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) (H.injective hH)
    exact hpl.symm ▸ hlC

end Homeomorph
