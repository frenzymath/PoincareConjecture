import PoincareConjecture.Proofs.M76.Mathlib.CoveringHomeomorphLift

set_option autoImplicit false

open Function Set unitInterval

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (hp : IsCoveringMap p)

theorem identityHomotopyLift_deck {f : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy f)
    (d : C(E, E)) (hd : p ∘ d = p) (t : I) (e : E) :
    hp.identityHomotopyLift H (t, d e) = d (hp.identityHomotopyLift H (t, e)) := by
  let L := hp.identityHomotopyLift H
  have hpaths : (fun s : I => L (s, d e)) = fun s => d (L (s, e)) := by
    refine hp.eq_of_comp_eq
      (L.continuous.comp (continuous_id.prodMk continuous_const))
      (d.continuous.comp (L.continuous.comp (continuous_id.prodMk continuous_const)))
      ?_ 0 ?_
    · funext s
      change p (L (s, d e)) = p (d (L (s, e)))
      calc
        p (L (s, d e)) = H (s, p (d e)) := hp.identityHomotopyLift_lifts H s (d e)
        _ = H (s, p e) := congrArg (fun x => H (s, x)) (congrFun hd e)
        _ = p (L (s, e)) := (hp.identityHomotopyLift_lifts H s e).symm
        _ = p (d (L (s, e))) := (congrFun hd (L (s, e))).symm
    · rw [hp.identityHomotopyLift_zero, hp.identityHomotopyLift_zero]
  exact congrFun hpaths t

theorem identityHomotopyLift_fixed {f : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy f) {e : E}
    (he : ∀ t, H (t, p e) = p e) (t : I) :
    hp.identityHomotopyLift H (t, e) = e := by
  have h := hp.const_of_comp (g := fun s : I => hp.identityHomotopyLift H (s, e))
    ((hp.identityHomotopyLift H).continuous.comp
      (continuous_id.prodMk continuous_const))
    (fun s s' => by
      simp only [identityHomotopyLift_lifts, he]) t 0
  exact h.trans (hp.identityHomotopyLift_zero H e)

include hp in

theorem exists_relative_homeomorph_lift (g : X ≃ₜ X) (S : Set X)
    (H : (ContinuousMap.id X).HomotopyRel ⟨g, g.continuous⟩ S) :
    ∃ G : E ≃ₜ E,
      (∀ e, p (G e) = g (p e)) ∧
      (∀ e, p e ∈ S → G e = e) ∧
      (∀ (d : C(E, E)), p ∘ d = p → ∀ e, G (d e) = d (G e)) ∧
      Nonempty ((ContinuousMap.id E).HomotopyRel ⟨G, G.continuous⟩ (p ⁻¹' S)) := by
  obtain ⟨G, hG⟩ := hp.exists_homeomorph_lift_of_homotopy g H.toHomotopy
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro e
    rw [hG, hp.identityHomotopyLift_lifts]
    exact H.apply_one _
  · intro e he
    rw [hG]
    exact hp.identityHomotopyLift_fixed H.toHomotopy (fun t => H.eq_fst t he) 1
  · intro d hd e
    rw [hG, hG]
    exact hp.identityHomotopyLift_deck H.toHomotopy d hd 1 e
  · exact ⟨{ toContinuousMap := hp.identityHomotopyLift H.toHomotopy
             map_zero_left := hp.identityHomotopyLift_zero H.toHomotopy
             map_one_left := fun e => (hG e).symm
             prop' := fun t e he =>
               hp.identityHomotopyLift_fixed H.toHomotopy (fun s => H.eq_fst s he) t }⟩

end IsCoveringMap
