import PoincareLib.Topology.Manifold.ConnectedSum.SphereFactors

/-!
# M73 factor classification statement

For a simply connected initial manifold, classify every exact non-survivor
factor of its M72 reconstruction as a positive spaceform and produce its
diffeomorphism to the unit three-sphere. The compactness and local geometric
certificates are supplied by the event-indexed M72 data. The theorem owns
the all-factor fundamental-group argument and positive uniformization;
M74 owns reduction of the connected-sum assembly.

Source: Morgan--Tian Proposition 15.3 and Corollary 15.4(2), pp. 357--359,
and Theorem 1.11(2), pp. 8--9. The separating/nonseparating-neck convention
is inherited from M38; see the surgery-extinction and analytic-outline
errata of 2026-09-10. Both sphere-bundle types over the circle are retained
until excluded using simple connectedness.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

def M73SphereFactorStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (C : M72ReconstructionConclusion I),
    Nonempty (M73SphereFactorConclusion I C)

end PoincareMT
