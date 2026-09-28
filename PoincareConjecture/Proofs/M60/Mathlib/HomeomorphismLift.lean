import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

namespace PoincareConjecture.M60

theorem exists_homeomorph_lift {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (e : X ≃ₜ X)
    (a b : E) (hab : p b = e (p a)) :
    ∃ H : E ≃ₜ E, H a = b ∧ ∀ x, p (H x) = e (p x) := by
  let f : C(E, X) := ⟨e ∘ p, e.continuous.comp hp.continuous⟩
  let g : C(E, X) := ⟨e.symm ∘ p, e.symm.continuous.comp hp.continuous⟩
  obtain ⟨F, ⟨hFa, hF⟩, _⟩ := hp.existsUnique_continuousMap_lifts f a b hab
  have hba : p a = g b := by
    change p a = e.symm (p b)
    rw [hab, e.symm_apply_apply]
  obtain ⟨G, ⟨hGb, hG⟩, _⟩ := hp.existsUnique_continuousMap_lifts g b a hba
  have hFx (x : E) : p (F x) = e (p x) := congrFun hF x
  have hGx (x : E) : p (G x) = e.symm (p x) := congrFun hG x
  have hGF : G ∘ F = id := by
    refine hp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id ?_ a ?_
    · funext x
      change p (G (F x)) = p x
      rw [hGx, hFx, e.symm_apply_apply]
    · change G (F a) = a
      rw [hFa, hGb]
  have hFG : F ∘ G = id := by
    refine hp.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id ?_ b ?_
    · funext x
      change p (F (G x)) = p x
      rw [hFx, hGx, e.apply_symm_apply]
    · change F (G b) = b
      rw [hGb, hFa]
  exact ⟨{ toFun := F
           invFun := G
           left_inv := fun x => congrFun hGF x
           right_inv := fun x => congrFun hFG x
           continuous_toFun := F.continuous
           continuous_invFun := G.continuous }, hFa, hFx⟩

end PoincareConjecture.M60
