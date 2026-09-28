import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.TorusTwistPL
import PoincareConjecture.Proofs.M76.Rigidity.HomeomorphInverseCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainComposition

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "T" => (Fin 2 → AddCircle (4 * (128 : ℝ)))

theorem exists_handle_winding_correction (f : C(H, H))
    (hfix : ∀ x ∈ B, f x = x) :
    ∃ n : Fin 2 → ℤ, Nonempty ((f.comp
      ⟨handleIntegerTwist n, (handleIntegerTwist n).continuous⟩).HomotopyRel
        (ContinuousMap.id H) B) := by
  let E := torusHandleCoordinates
  let f' : C(unitInterval × T, unitInterval × T) :=
    (⟨E, E.continuous⟩ : C(H, unitInterval × T)).comp
      (f.comp ⟨E.symm, E.symm.continuous⟩)
  have hboundary (z : unitInterval × T) (hz : z.1 = 0 ∨ z.1 = 1) : f' z = z := by
    have hb : E.symm z ∈ B := (torusHandleCoordinates_boundary _).mpr (by
      change (E (E.symm z)).1 = 0 ∨ (E (E.symm z)).1 = 1
      rwa [E.apply_symm_apply])
    change E (f (E.symm z)) = z
    rw [hfix _ hb, E.apply_symm_apply]
  obtain ⟨n, ⟨G⟩⟩ := exists_torus_winding_correction f'
    (fun z => hboundary (0, z) (Or.inl rfl))
    (fun z => hboundary (1, z) (Or.inr rfl))
  refine ⟨n, ⟨{
    toFun := fun z => E.symm (G (z.1, E z.2))
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    rw [G.apply_zero]
    change E.symm (E (f (E.symm (torusIntegerTwist n (E x))))) = f (handleIntegerTwist n x)
    rw [E.symm_apply_apply]
    rfl
  · intro x
    rw [G.apply_one]
    exact E.symm_apply_apply x
  · intro t x hx
    change E.symm (G (t, E x)) = f (handleIntegerTwist n x)
    rw [G.eq_fst t ((torusHandleCoordinates_boundary x).mp hx)]
    change E.symm (E (f (E.symm (torusIntegerTwist n (E x))))) = f (handleIntegerTwist n x)
    rw [E.symm_apply_apply]
    rfl

theorem exists_relative_endpoint_of_standard_to_source
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (g : H ≃ₜ H)
    (hg : ChartwisePLMap d e ⟨latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g,
      (latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g).continuous⟩)
    (hfix : ∀ x ∈ B, g x = x)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ h : H ≃ₜ H,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L h) ∧
      Nonempty (phi.HomotopyRel ⟨h, h.continuous⟩ B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel ⟨h, h.continuous⟩ B) := by
  obtain ⟨n, ⟨G⟩⟩ := exists_handle_winding_correction ⟨g, g.continuous⟩ hfix
  let k : H ≃ₜ H := (handleIntegerTwist n).trans g
  let K := latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L k
  have hK : ChartwisePLMap d e ⟨K, K.continuous⟩ := by
    have hcomp := hg.comp (chartwisePLMap_handleIntegerTwist hd n)
    have heq : (⟨latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g,
        (latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L g).continuous⟩ : C(R, R)).comp
        (latticeHandleMapInDomain (Fin 1) (Fin 2) L
          ⟨handleIntegerTwist n, (handleIntegerTwist n).continuous⟩) = ⟨K, K.continuous⟩ := by
      apply ContinuousMap.ext
      intro x
      change (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (g ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L)
          ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm _))) = _
      rw [Homeomorph.apply_symm_apply]
      rfl
    simpa only [heq, preimage_univ, inter_univ, ChartwisePLMap] using hcomp
  let G' : (ContinuousMap.id H).HomotopyRel ⟨k.symm, k.symm.continuous⟩ B := {
    toFun := fun z => k.symm (G z)
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro x
      rw [G.apply_zero]
      exact k.symm_apply_apply x
    map_one_left := by intro x; rw [G.apply_one]; rfl
    prop' := by
      intro t x hx
      change k.symm (G (t, x)) = x
      rw [G.eq_fst t hx]
      exact k.symm_apply_apply x }
  refine ⟨k.symm, ?_, ⟨F.symm.trans G'⟩, ⟨G'⟩⟩
  change ChartwisePLHomeomorph e d K.symm
  exact hK.inverse_homeomorph.chartwisePLHomeomorph

end PoincareConjecture.M76.HamiltonIntervalTorus
