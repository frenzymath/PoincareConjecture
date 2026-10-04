import PoincareLib.Topology.Manifold.ConnectedSum.Reconstruction
import PoincareLib.Topology.Manifold.Surgery.SphereFactors.Assembly.SliceSimplyConnected
import PoincareLib.Topology.Manifold.Surgery.SphereFactors.Assembly.PieceSimplyConnected

/-!
# Kind classification for the exact M72 summands

The M72 ledger indexes precisely the non-survivor event pieces.  The assembly
factor theorem makes each such piece simply connected.  Once the independent
sphere-bundle obstruction is supplied, case analysis on the three-way surgery
kind therefore leaves only the positive-spaceform case.

Source: Morgan--Tian Proposition 15.3 and Corollary 15.4(2), pp. 357--359.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

set_option linter.style.haveILetI false in
/-- The M72 non-survivor ledger contains only positive spaceforms after the
piece simple-connectedness argument excludes survivors and sphere bundles.
Source: Morgan--Tian Corollary 15.4(2), pp. 358--359. -/
theorem m73_factor_kind
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (C : M72ReconstructionConclusion I)
    (bundle_obstruction :
      ∀ {D : GeneralizedSliceCarrier.{u}} (_B : SurgerySphereBundle D)
        (_hc : IsCompact (Set.univ : Set D.carrier)),
        ¬ SimplyConnectedSpace D.carrier) :
    ∀ j : Fin C.summand_count,
      (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.kind
        (C.summand_index j).2.1 = .spaceform := by
  letI : SimplyConnectedSpace (I.global.certificate.flow.slice 0).carrier :=
    m73_sliceZero_simplyConnected I
  intro j
  have hconn : IsConnected (Set.univ : Set (C.pieces j).carrier) := by
    rw [C.piece_eq j]
    exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.piece_connected
      (C.summand_index j).2.1
  letI : SimplyConnectedSpace (C.pieces j).carrier :=
    C.assembly.piece_simplyConnected j hconn
  cases hkind : (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.kind
      (C.summand_index j).2.1 with
  | survivor =>
      exact (C.piece_kind j hkind).elim
  | sphereBundle =>
      exfalso
      have hb : Nonempty (SurgerySphereBundle (C.pieces j)) := by
        rw [C.piece_eq j]
        exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.bundles
          (C.summand_index j).2.1 hkind
      have hc : IsCompact (Set.univ : Set (C.pieces j).carrier) := by
        rw [C.piece_eq j]
        exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.piece_compact
          (C.summand_index j).2.1
      exact bundle_obstruction (Classical.choice hb) hc (by infer_instance)
  | spaceform => rfl

end PoincareMT
