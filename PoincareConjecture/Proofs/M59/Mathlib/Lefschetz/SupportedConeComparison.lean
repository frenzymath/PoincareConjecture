import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SupportedLiftRestriction
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.TrivialLiftComparison
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.OrderComplexCone
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.ContractibleCovering

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open scoped Simplicial unitInterval

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (hp : IsCoveringMap p) (H : C(I × X, X))
  (hzero : ∀ x, H (0, x) = x) (x₀ : X) (hone : ∀ x, H (1, x) = x₀)
  (hfixed : ∀ t, H (t, x₀) = x₀)

include hfixed in
set_option backward.isDefEq.respectTransparency false in

theorem coveringFiberRetraction_chainMap_quasiIso :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom (coveringFiberRetraction p hp H hzero x₀ hone)))
        integralCoefficient.{u}) := by
  let equiv := (coveringDeformationEquiv p hp H hzero {x₀} hone
    (fun x hx t => by
      have hx' : x = x₀ := hx
      subst x
      exact hfixed t)).symm
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (integralHomologyIsoOfHomotopyEquiv equiv n).hom
  infer_instance

variable {J : Type u} [PartialOrder J] [Fintype J]

set_option backward.isDefEq.respectTransparency false in

theorem supportedSingularComparison_cone_quasiIso
    (p : C(E, (finiteOrderComplex J).space)) (hp : IsCoveringMap p)
    (s : Finset J) (v : J) (hv : v ∈ s) (hmin : ∀ j ∈ s, v ≤ j) :
    QuasiIso (SSet.chainComplexMap (supportedSingularComparison p s)
      integralCoefficient.{u}) := by
  let p' := liftedCoordinateProjection p s
  have hp' : IsCoveringMap p' := hp.restrictPreimage (orderComplexNeighborhood s)
  let H := orderComplexConeHomotopy s v hv hmin
  let x₀ := orderComplexConePoint s v hv
  let F := p' ⁻¹' {x₀}
  let : DiscreteTopology F := (hp' x₀).discreteTopology_fiber
  let e := contractibleCoveringHomeomorph p' hp' H.toContinuousMap
    H.map_zero_left x₀ H.map_one_left
  have hret : QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (coveringProductRetraction e)))
        integralCoefficient.{u}) :=
    coveringFiberRetraction_chainMap_quasiIso p' hp' H.toContinuousMap
      H.map_zero_left x₀ H.map_one_left
      (orderComplexConeHomotopy_fixed s v hv hmin)
  let := singularLiftConeComparison_quasiIso s v hv hmin p'
    (orderComplexSupportedSingular s) e (fun _ => rfl) hret
  let T := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integralCoefficient
  have h := supportedLiftRestrictionIso_projection p s
  change QuasiIso (T.map (supportedSingularComparison p s))
  rw [← h, Functor.map_comp]
  infer_instance

end PoincareConjecture.Proofs.M59
