import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Module.Basic









set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E]




theorem norm_closedExtension_sub_le {S : Set E} (g : S ≃ₜ S) (hS : IsClosed S)
    (hfront : ∀ x : S, (x : E) ∈ frontier S → g x = x) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x : S, ‖(g x : E) - x‖ ≤ C) (x : E) :
    ‖g.closedExtension hS hfront x - x‖ ≤ C := by
  by_cases hx : x ∈ S
  · rw [g.closedExtension_apply_mem hS hfront hx]
    exact hbound ⟨x, hx⟩
  · rw [g.closedExtension_apply_notMem hS hfront hx, sub_self, norm_zero]
    exact hC




theorem compactified_conjugate_fixed_relative
    (p : OpenPartialHomeomorph E E)
    {S : Set E} (hpS : MapsTo p S S) (g H : E ≃ₜ E)
    (hg : ∀ x ∉ S, g x = x) (hconj : ∀ x, H (p x) = p (g x))
    (houtside : ∀ y ∉ p.target, H y = y) :
    ∀ y ∈ Sᶜ ∪ frontier S, H y = y := by
  have hfix : EqOn H id Sᶜ := by
    intro y hy
    by_cases hyt : y ∈ p.target
    · have hxy : p (p.symm y) = y := p.right_inv hyt
      have hxS : p.symm y ∉ S := fun hx => hy (hxy ▸ hpS hx)
      calc
        H y = H (p (p.symm y)) := congrArg H hxy.symm
        _ = p (g (p.symm y)) := hconj _
        _ = y := by rw [hg _ hxS, hxy]
    · exact houtside y hyt
  intro y hy
  rcases hy with hy | hy
  · exact hfix hy
  · exact hfix.closure H.continuous continuous_id
      (frontier_eq_closure_inter_closure (s := S) ▸ hy).2

end Homeomorph
