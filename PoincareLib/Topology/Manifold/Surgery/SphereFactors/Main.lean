import PoincareLib.Topology.Manifold.Surgery.SphereFactors.Statement
import PoincareLib.Topology.Manifold.Surgery.SphereFactors.Assembly.FactorKind
import PoincareLib.Topology.Manifold.Surgery.SphereFactors.Assembly.SphereBundleExclusion
import PoincareLib.Topology.Manifold.Surgery.SphereFactors.SimplyConnected.KillingHopf

/-!
# M73 proof entry

The single admission owns componentwise van Kampen over the actual finite
assembly, the sphere-bundle obstruction, and positive uniformization.
Earlier contracts remain read-only for its proof owner.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

set_option linter.style.haveILetI false in
/-- Given the M72 reconstruction of a simply connected initial manifold,
every indexed non-survivor event piece has kind `spaceform` and admits a
smooth diffeomorphism to the unit three-sphere. Transport simple connectedness
through the initial identification and apply van Kampen to all assembly
factors. A sphere bundle over the circle has a nontrivial fundamental group;
every remaining compact positive spaceform is complete and is a sphere by
uniformization. No additional orientation or completeness is assumed.
Source: Morgan--Tian Corollary 15.4(2), pp. 358--359, Proposition 15.3,
pp. 357--358, and Theorem 1.11(2), pp. 8--9. The M38 neck-separation erratum
is retained in the actual local factors; both bundle types are excluded. -/
theorem m73SphereFactors : M73SphereFactorStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ _ N I C
  letI : SimplyConnectedSpace (I.global.certificate.flow.slice 0).carrier :=
    m73_sliceZero_simplyConnected I
  have hkind := m73_factor_kind I C
    (fun B hc => SurgerySphereBundle.not_simplyConnectedSpace B hc)
  refine ⟨{ factor_kind := hkind, factor_sphere := ?_ }⟩
  intro j
  have hconn : IsConnected (Set.univ : Set (C.pieces j).carrier) := by
    rw [C.piece_eq j]
    exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.piece_connected
      (C.summand_index j).2.1
  letI : SimplyConnectedSpace (C.pieces j).carrier :=
    C.assembly.piece_simplyConnected j hconn
  have hs : Nonempty (SurgeryPositiveSpaceform (C.pieces j)) := by
    rw [C.piece_eq j]
    exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.spaceforms
      (C.summand_index j).2.1 (hkind j)
  exact Classical.choice (Classical.choice hs).nonempty_diffeomorph_threeSphere

end PoincareMT
