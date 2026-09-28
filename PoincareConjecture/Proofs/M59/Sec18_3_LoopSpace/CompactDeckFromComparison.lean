import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CoverFreeClasses
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CompactDeck.LiftedModel
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.OrderComplexUniverse
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.OrderComplexSimplex
import PoincareConjecture.Proofs.M02.Topology.ThreeManifoldTriangulation













set_option autoImplicit false

open CategoryTheory HomologicalComplex
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M02.Topology Proofs.M59





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

end PoincareConjecture
