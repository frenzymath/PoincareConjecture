import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.ComparisonGluing
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SupportedComparison
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.NeighborhoodSubspaces











set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]
  {E : Type u} [TopologicalSpace E] (p : C(E, (finiteOrderComplex J).space))

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in




theorem supportedSingularComparison_minimal_gluing
    (s : Finset J) (v : J) (hminimal : ∀ j ∈ s, j ≤ v → j = v)
    (ha : QuasiIso (SSet.chainComplexMap
      (supportedSingularComparison p (s.erase v)) integralCoefficient.{u}))
    (hb : QuasiIso (SSet.chainComplexMap
      (supportedSingularComparison p (s.filter (v ≤ ·))) integralCoefficient.{u}))
    (hl : QuasiIso (SSet.chainComplexMap
      (supportedSingularComparison p (s.filter (v < ·))) integralCoefficient.{u})) :
    QuasiIso (SSet.chainComplexMap (supportedSingularComparison p s)
      integralCoefficient.{u}) := by
  classical
  let a := s.erase v
  let b := s.filter (v ≤ ·)
  let l := s.filter (v < ·)
  let D := fun t => supportedSingularLift p (orderComplexSingular J) t
  let W := fun t => liftedCoordinateNeighborhood p t
  have hA : W a ⊆ W s := fun _ hx =>
    orderComplexNeighborhood_mono (Finset.erase_subset v s) hx
  have hB : W b ⊆ W s := fun _ hx =>
    orderComplexNeighborhood_mono (Finset.filter_subset _ _) hx
  have hUnion : W a ∪ W b = W s := by
    change p ⁻¹' orderComplexNeighborhood a ∪ p ⁻¹' orderComplexNeighborhood b = _
    rw [← Set.preimage_union, orderComplexNeighborhood_minimal_union]
    rfl
  have hInter : W a ∩ W b = W l := by
    change p ⁻¹' orderComplexNeighborhood a ∩ p ⁻¹' orderComplexNeighborhood b = _
    rw [← Set.preimage_inter, orderComplexNeighborhood_minimal_inter s v hminimal]
    rfl
  let U : Set (W s) := Subtype.val ⁻¹' W a
  let V : Set (W s) := Subtype.val ⁻¹' W b
  have hU : IsOpen U := (isOpen_orderComplexNeighborhood a).preimage
    (p.continuous.comp continuous_subtype_val)
  have hV : IsOpen V := (isOpen_orderComplexNeighborhood b).preimage
    (p.continuous.comp continuous_subtype_val)
  have hcover : U ∪ V = Set.univ :=
    Set.eq_univ_of_forall (fun x => show x.val ∈ W a ∪ W b from hUnion.symm ▸ x.property)
  let eA := nestedSubsetHomeomorph (W s) (W a) hA
  let eB := nestedSubsetHomeomorph (W s) (W b) hB
  let eL := intersectionSubsetHomeomorph (W s) (W a) (W b) (W l) hA hInter
  let χA := supportedSingularComparison p a ≫ TopCat.toSSet.map
    (TopCat.ofHom (⟨eA, eA.continuous⟩ : C(W a, U)))
  let χB := supportedSingularComparison p b ≫ TopCat.toSSet.map
    (TopCat.ofHom (⟨eB, eB.continuous⟩ : C(W b, V)))
  let χL := supportedSingularComparison p l ≫ TopCat.toSSet.map
    (TopCat.ofHom (⟨eL, eL.continuous⟩ : C(W l, ↥(U ∩ V))))
  let sq : SSet.Subcomplex.BicartSq (D l) (D a) (D b) (D s) := {
    sup_eq := supportedSingularLift_minimal_union p (orderComplexSingular J) s v hminimal
    inf_eq := by
      have h := congrArg (fun A : (nerve J).Subcomplex =>
        A.preimage (singularLiftBase p (nerve J) (orderComplexSingular J)))
          (supportedNerve_minimal_inter s v)
      exact h }
  apply simplicialComparison_quasiIso_of_openCover U V hU hV hcover sq
    χL χA χB (supportedSingularComparison p s)
  · ext n : 1
    apply ConcreteCategory.hom_ext
    intro z
    apply ((TopCat.of U).toSSetObjEquiv n).injective
    rfl
  · ext n : 1
    apply ConcreteCategory.hom_ext
    intro z
    apply ((TopCat.of V).toSSetObjEquiv n).injective
    rfl
  · ext n : 1
    apply ConcreteCategory.hom_ext
    intro z
    apply ((TopCat.of (W s)).toSSetObjEquiv n).injective
    rfl
  · ext n : 1
    apply ConcreteCategory.hom_ext
    intro z
    apply ((TopCat.of (W s)).toSSetObjEquiv n).injective
    rfl
  · let := hl
    let := homeomorphSingularChainMap_quasiIso eL
    change QuasiIso (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficient).map (_ ≫ _))
    rw [Functor.map_comp]
    infer_instance
  · let := ha
    let := homeomorphSingularChainMap_quasiIso eA
    change QuasiIso (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficient).map (_ ≫ _))
    rw [Functor.map_comp]
    infer_instance
  · let := hb
    let := homeomorphSingularChainMap_quasiIso eB
    change QuasiIso (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficient).map (_ ≫ _))
    rw [Functor.map_comp]
    infer_instance

end PoincareConjecture.Proofs.M59
