import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.CoverFreeClasses
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.CompactDeck.LiftedModel
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexUniverse
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexSimplex
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# From the characteristic comparison to the compact deck conclusion

M02 supplies an actual finite triangulation of the base manifold. Relabel
its vertices into the covering universe, compose the covering projection
with that homeomorphism's inverse, and use the literal lifted singular
model. Its finite-model trace calculation applies the supplied M02 provider
to the covering manifold. The only remaining premise is the specific
characteristic projection's quasi-isomorphism.
Source: Hatcher, Theorems 2.27 and 2C.3; MT Claim 18.16, printed p. 430.
-/

set_option autoImplicit false

open CategoryTheory HomologicalComplex
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

open Proofs.M02.Topology Proofs.M59

/-- The literal characteristic comparison for every finite order-complex
cover completes the compact deck-action calculation. M02 is applied to
the cover in the finite-model theorem, and its actual finite triangulation
is applied to the base here. Source: Hatcher 2.27 and 2C.3; MT p. 430. -/
theorem m59CompactCoverDeckAction_of_orderComplexComparison
    (P02 : RepairedClosedTopologyProvider.{u})
    (hcomparison : ∀ (J : Type u) [PartialOrder J] [Fintype J]
      {E : Type u} [TopologicalSpace E] (p : C(E, (finiteOrderComplex J).space)),
      IsCoveringMap p → QuasiIso (SSet.chainComplexMap
        (singularLiftProjection p (nerve J) (orderComplexSingular J)) integralCoefficient.{u})) :
    M59CompactCoverDeckAction.{u} := by
  intro M E _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp d hd c r a
  obtain ⟨J, hJ, fJ, ⟨e⟩, _⟩ := exists_compact_three_manifold_finite_triangulation (M := M)
  let := hJ
  let := fJ
  let e' : (finiteOrderComplex (ULift.{u} J)).space ≃ₜ M :=
    (orderComplexULiftHomeomorph J).trans e
  let p' : C(E, (finiteOrderComplex (ULift.{u} J)).space) :=
    ⟨fun z => e'.symm (p z), e'.symm.continuous.comp p.continuous⟩
  have hp' : IsCoveringMap p' := hp.homeomorph_comp e'.symm
  have hd' : p'.comp d = p' := by
    ext z : 1
    exact congrArg e'.symm (ContinuousMap.congr_fun hd z)
  exact compactThree_deck_piThreeMap_eq_transport_of_liftComparison
    P02 p' hp' (ULift.{u} J) (orderComplexSingular (ULift.{u} J))
    (hcomparison _ p' hp') d hd' c r a

end PoincareMT
