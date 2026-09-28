import PoincareConjecture.Proofs.M76.Mathlib.CoveringLiftRelative

set_option autoImplicit false

open Set unitInterval

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (hp : IsCoveringMap p)

include hp

theorem exists_relative_deformation_lift {A : Set X} {f : C(X, X)}
    (H : (ContinuousMap.id X).HomotopyRel f A) (hf : ∀ x, f x ∈ A) :
    ∃ (g : C(E, E)) (L : (ContinuousMap.id E).HomotopyRel g (p ⁻¹' A)),
      (∀ (t : I) (e : E), p (L (t, e)) = H (t, p e)) ∧
      range g = p ⁻¹' A := by
  let T := hp.identityHomotopyLift H.toHomotopy
  let g : C(E, E) :=
    ⟨fun e => T (1, e), T.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let L : (ContinuousMap.id E).HomotopyRel g (p ⁻¹' A) :=
    { toContinuousMap := T
      map_zero_left := hp.identityHomotopyLift_zero H.toHomotopy
      map_one_left := fun _ => rfl
      prop' := fun t e he =>
        hp.identityHomotopyLift_fixed H.toHomotopy (fun s => H.eq_fst s he) t }
  refine ⟨g, L, hp.identityHomotopyLift_lifts H.toHomotopy, ?_⟩
  ext e
  constructor
  · rintro ⟨z, rfl⟩
    change p (T (1, z)) ∈ A
    rw [hp.identityHomotopyLift_lifts H.toHomotopy, H.toHomotopy.apply_one]
    exact hf (p z)
  · intro he
    exact ⟨e, hp.identityHomotopyLift_fixed H.toHomotopy (fun s => H.eq_fst s he) 1⟩

theorem isConnected_preimage_of_deformation [ConnectedSpace E]
    {A : Set X} {f : C(X, X)}
    (H : (ContinuousMap.id X).HomotopyRel f A) (hf : ∀ x, f x ∈ A) :
    IsConnected (p ⁻¹' A) := by
  obtain ⟨g, _, _, hg⟩ := hp.exists_relative_deformation_lift H hf
  rw [← hg]
  exact isConnected_range g.continuous

end IsCoveringMap
