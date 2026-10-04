import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.CoveringLiftRelative

/-!

# Lifting strong deformations through covering maps

The homotopy lift from the identity fixes the whole preimage
of the retained set. Its endpoint range is exactly that full
preimage, which is therefore connected when the total space
is connected. See Hatcher, Theorem 3.1 proof, p. 45 and
M76 derivation 270.
-/

set_option autoImplicit false

open Set unitInterval

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (hp : IsCoveringMap p)

include hp

/-- A strong deformation lifts from the identity to a strong
deformation onto the entire preimage of its retained set.
The complete projection formula and exact endpoint range
are retained. Covering surjectivity is unnecessary.
See Hatcher Theorem 3.1, p. 45 and M76 derivation 270. -/
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

/-- The complete inverse image of a strong deformation
retract is connected whenever the covering total space is
connected. This supplies the connected lifted image used in
Hatcher's tower. See Theorem 3.1, p. 45 and M76 derivation 270. -/
theorem isConnected_preimage_of_deformation [ConnectedSpace E]
    {A : Set X} {f : C(X, X)}
    (H : (ContinuousMap.id X).HomotopyRel f A) (hf : ∀ x, f x ∈ A) :
    IsConnected (p ⁻¹' A) := by
  obtain ⟨g, _, _, hg⟩ := hp.exists_relative_deformation_lift H hf
  rw [← hg]
  exact isConnected_range g.continuous

end IsCoveringMap
