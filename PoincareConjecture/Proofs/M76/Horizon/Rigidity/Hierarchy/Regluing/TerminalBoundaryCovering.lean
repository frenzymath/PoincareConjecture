import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalCoordinatePL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBoxDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.BoundaryLocalHomeomorph

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem isCoveringMap_hamiltonZero_terminal_boundary
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N) (hne : N.Nonempty)
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (boundaryMap : C(frontier N, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)))
    (hvalue : ∀ x : frontier N, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : (ℝ × ℝ) × ℝ).1.1) : C0),
        (((boundaryMap x : (ℝ × ℝ) × ℝ).1.2) : C0)),
        (((boundaryMap x : (ℝ × ℝ) × ℝ).2) : C0)))
    (hinj : IsLocallyInjective (fun x : frontier N => hamiltonZeroAmbientMap phi x)) :
    IsCoveringMap boundaryMap := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨s, A, HB, j, lift, _, hj, hjval, hlift, hliftval⟩ :=
    exists_hamiltonZero_finitePL_boundary_coordinates hd hphi he hN hne
      huv hab halpha hthird hsecond hfirst boundaryMap hvalue
  have hlocal : IsLocallyInjective boundaryMap := by
    intro x
    obtain ⟨U, hU, hxU, hi⟩ := hinj x
    refine ⟨U, hU, hxU, ?_⟩
    intro y hy z hz hyz
    apply hi hy hz
    apply (Q0).injective
    rw [hvalue y, hvalue z, hyz]
  exact isCoveringMap_frontier_of_polyhedral_model he
    (plDomain_terminalBox huv hab halpha) hN HB j hj hjval lift
    (polyhedralPL_terminalBoxAtlas_of_finitePiecewiseAffineOn hlift)
    boundaryMap hliftval hlocal

end PoincareConjecture.M76
