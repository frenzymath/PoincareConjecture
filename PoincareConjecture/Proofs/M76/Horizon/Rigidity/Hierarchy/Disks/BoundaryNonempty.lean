import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhaseArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateLifts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_annulus_covering_surjective
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c) :
    Function.Surjective c := by
  let : Fact (0 < (4 * (8 : ℝ))) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  have hrange : (range c).Nonempty :=
    ⟨c ⟨(0, 0), by norm_num [squareAnnulus]⟩, ⟨⟨(0, 0), by norm_num [squareAnnulus]⟩, rfl⟩⟩
  exact range_eq_univ.mp (IsClopen.eq_univ
    ⟨(isCompact_range c.continuous).isClosed, hc.isOpenMap.isOpen_range⟩ hrange)

theorem hamiltonZero_installed_annulus_third_boundary_levels_nonempty
    (phi : C(H0, H0)) {R : Set X0}
    (j : ℝ × ℝ → X0) (hj : j '' Ann ⊆ frontier R)
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (delta0 delta1 : ℝ) (theta : C0)
    (hvalue : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) :
    ∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {xi}).Nonempty := by
  intro xi
  obtain ⟨z, hz⟩ := hamiltonZero_annulus_covering_surjective c hc (0, xi)
  refine ⟨j z, hj ⟨z, z.property, rfl⟩, ?_⟩
  change hamiltonZeroThirdCircleMap phi (j z) = xi
  rw [hamiltonZeroThirdCircleMap_ambient, hvalue, hz,
    hamiltonZeroAnnulusTargetMap_coordinates]

end PoincareConjecture.M76
