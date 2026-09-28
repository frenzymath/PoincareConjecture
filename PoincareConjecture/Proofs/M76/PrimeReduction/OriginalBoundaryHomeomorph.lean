import Mathlib.Topology.Homeomorph.Lemmas









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76




theorem exists_original_boundary_homeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {R : Set X} {A T : Set E} (hAT : A ⊆ T) (hFR : frontier R ⊆ R)
    (H : R ≃ₜ T) (g : E → R)
    (hg : ∀ z : T, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ T, (g z : X) ∈ frontier R ↔ z ∈ A) :
    ∃ HB : A ≃ₜ frontier R,
      (∀ z : A, (HB z : X) = (g z : X)) ∧
      ∀ x : frontier R, (HB.symm x : E) = (H ⟨x, hFR x.property⟩ : E) := by
  have hgm (x : R) : g (H x) = x := by
    apply Subtype.ext
    rw [hg (H x), H.symm_apply_apply]
  let f : A → frontier R := fun z =>
    ⟨H.symm (Set.inclusion hAT z), by
      rw [← hg (Set.inclusion hAT z)]
      exact (hboundary z (hAT z.property)).mpr z.property⟩
  let k : frontier R → A := fun x =>
    ⟨H ⟨x, hFR x.property⟩, by
      apply (hboundary _ (H ⟨x, hFR x.property⟩).property).mp
      rw [hgm]
      exact x.property⟩
  let HB : A ≃ₜ frontier R :=
    { toFun := f
      invFun := k
      left_inv := by
        intro z
        apply Subtype.ext
        change (H (H.symm (Set.inclusion hAT z)) : E) = (z : E)
        exact congrArg (fun y : T => (y : E)) (H.apply_symm_apply (Set.inclusion hAT z))
      right_inv := by
        intro x
        apply Subtype.ext
        change (H.symm (H ⟨x, hFR x.property⟩) : X) = (x : X)
        exact congrArg (fun y : R => (y : X)) (H.symm_apply_apply ⟨x, hFR x.property⟩)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp
          (H.symm.continuous.comp (continuous_inclusion hAT))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp
          (H.continuous.comp (continuous_inclusion hFR)) }
  exact ⟨HB, fun z => (hg (Set.inclusion hAT z)).symm, fun _ => rfl⟩

end PoincareConjecture.M76
