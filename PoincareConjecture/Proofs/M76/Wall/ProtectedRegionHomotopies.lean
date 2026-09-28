import Mathlib.Topology.Homotopy.Path










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76




theorem exists_frontier_loop_homotopy_in_protected_region
    {X : Type*} [TopologicalSpace X] {R C F : Set X}
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (x : (R \ C : Set X)) (p : Path x x) (hp : ∀ t, (p t : X) ∈ F) :
    Nonempty (p.Homotopy (Path.refl x)) := by
  let v : (R \ C : Set X) → R := fun y => ⟨y, y.property.1⟩
  have hv : Continuous v := continuous_subtype_val.subtype_mk _
  let q : Path (v x) (v x) := p.map hv
  obtain ⟨H, hH⟩ := hloops (v x) q (fun t => hp t)
  let G : p.Homotopy (Path.refl x) :=
    { toFun := fun z => ⟨(H z : X), (H z).property, hH z⟩
      continuous_toFun :=
        (continuous_subtype_val.comp H.continuous).subtype_mk _
      map_zero_left := by
        intro t
        apply Subtype.ext
        exact congrArg (Subtype.val : R → X) (H.apply_zero t)
      map_one_left := by
        intro t
        apply Subtype.ext
        exact congrArg (Subtype.val : R → X) (H.apply_one t)
      prop' := by
        intro t s hs
        apply Subtype.ext
        exact congrArg (Subtype.val : R → X) (H.eq_fst t hs) }
  exact ⟨G⟩

end PoincareConjecture.M76
