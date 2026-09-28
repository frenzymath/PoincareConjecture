import PoincareConjecture.Proofs.M76.Wall.ProtectedRegionHomotopies









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76



theorem exists_avoiding_frontier_loop_homotopy_of_inclusion_null
    {X : Type*} [TopologicalSpace X] {R C F : Set X}
    (hF : F ⊆ R \ C)
    (hloops : ∀ (x : F) (p : Path x x),
      (p.map (ContinuousMap.inclusion hF).continuous).Homotopic
        (Path.refl ((ContinuousMap.inclusion hF) x)))
    (x : R) (p : Path x x) (hp : ∀ t, (p t : X) ∈ F) :
    ∃ H : p.Homotopy (Path.refl x), ∀ z, (H z : X) ∉ C := by
  have hx : (x : X) ∈ F := by simpa only [p.source] using hp 0
  let y : F := ⟨x, hx⟩
  let q : Path y y :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun :=
        (continuous_subtype_val.comp p.continuous).subtype_mk _
      source' := Subtype.ext (congrArg (Subtype.val : R → X) p.source)
      target' := Subtype.ext (congrArg (Subtype.val : R → X) p.target) }
  obtain ⟨G⟩ := hloops y q
  let H : p.Homotopy (Path.refl x) :=
    { toFun := fun z => ⟨(G z : X), (G z).property.1⟩
      continuous_toFun :=
        (continuous_subtype_val.comp G.continuous).subtype_mk _
      map_zero_left := by
        intro t
        apply Subtype.ext
        exact congrArg (Subtype.val : (R \ C : Set X) → X) (G.apply_zero t)
      map_one_left := by
        intro t
        apply Subtype.ext
        exact congrArg (Subtype.val : (R \ C : Set X) → X) (G.apply_one t)
      prop' := by
        intro t s hs
        apply Subtype.ext
        exact congrArg (Subtype.val : (R \ C : Set X) → X) (G.eq_fst t hs) }
  exact ⟨H, fun z => (G z).property.2⟩



theorem protected_frontier_loop_contractions_iff
    {X : Type*} [TopologicalSpace X] {R C F : Set X}
    (hF : F ⊆ R \ C) :
    (∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ↔
    (∀ (x : F) (p : Path x x),
      (p.map (ContinuousMap.inclusion hF).continuous).Homotopic
        (Path.refl ((ContinuousMap.inclusion hF) x))) := by
  constructor
  · intro hloops x p
    exact exists_frontier_loop_homotopy_in_protected_region hloops
      ((ContinuousMap.inclusion hF) x)
      (p.map (ContinuousMap.inclusion hF).continuous) (fun t => (p t).property)
  · intro hloops x p hp
    exact exists_avoiding_frontier_loop_homotopy_of_inclusion_null hF hloops x p hp

end PoincareConjecture.M76
