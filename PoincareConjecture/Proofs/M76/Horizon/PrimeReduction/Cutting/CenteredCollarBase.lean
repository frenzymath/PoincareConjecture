import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Lemmas



set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_centered_collar_base_homeomorph
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A] {N S : Set X}
    (W : (A × unitInterval) ≃ₜ N) (hSN : S ⊆ N)
    (hcenter : ∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2) :
    ∃ H : A ≃ₜ S, ∀ a, (H a : X) = W (a,⟨1/2,by norm_num⟩) := by
  let mid : unitInterval := ⟨1/2,by norm_num⟩
  let f : A → S := fun a => ⟨W (a,mid),(hcenter (a,mid)).mpr rfl⟩
  let g : S → A := fun s => ((W.symm ⟨s,hSN s.property⟩)).1
  have hleft : Function.LeftInverse g f := by
    intro a
    change (W.symm (W (a,mid))).1 = a
    rw [W.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro s
    have ht : (W.symm ⟨s,hSN s.property⟩).2 = mid := by
      apply Subtype.ext
      apply (hcenter _).mp
      simpa only [W.apply_symm_apply] using s.property
    apply Subtype.ext
    change (W ((W.symm ⟨s,hSN s.property⟩).1,mid) : X) = s
    rw [← ht,Prod.mk.eta,W.apply_symm_apply]
  let H : A ≃ₜ S :=
    { toEquiv := ⟨f,g,hleft,hright⟩
      continuous_toFun := by unfold f; fun_prop
      continuous_invFun := by unfold g; fun_prop }
  exact ⟨H,fun _ => rfl⟩

end PoincareConjecture.M76
