import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CompactDeck.FiniteModel
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.FiniteLiftChains
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SingularLiftDeck
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.NormalizedComparison
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.FixedPointFree












set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable (P02 : RepairedClosedTopologyProvider.{u})
  {E : Type u} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [IsManifold (𝓡 3) ∞ E] [T2Space E] [SecondCountableTopology E]
  [CompactSpace E] [SimplyConnectedSpace E]
  {X : Type u} [TopologicalSpace X] [T2Space X]
  (p : C(E, X)) (hp : IsCoveringMap p)
  (J : Type u) [PartialOrder J] [Finite J]
  (χ : nerve J ⟶ TopCat.toSSet.obj (TopCat.of X))

include P02 hp

set_option backward.isDefEq.respectTransparency false in



theorem compactThree_deck_homologyMap_eq_id_of_liftComparison
    (hcomparison : QuasiIso (SSet.chainComplexMap
      (singularLiftProjection p (nerve J) χ) integralCoefficient.{u}))
    (d : C(E, E)) (hd : p.comp d = p) :
    surgeryThirdHomologyMap d = LinearMap.id := by
  classical
  let := Fintype.ofFinite J
  by_cases hid : d = ContinuousMap.id E
  · subst d
    change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
      integralCoefficient).map (𝟙 (TopCat.of E))).hom = _
    exact congrArg (fun f : surgeryThirdHomology E ⟶ surgeryThirdHomology E => f.hom)
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
        integralCoefficient).map_id (TopCat.of E))
  let D := singularLiftSSet p (nerve J) χ
  let F := SSet.normalizedChainComplexMap (singularLiftDeck p (nerve J) χ d hd)
    integralCoefficient
  let c := normalizedSingularComparison (singularLiftProjection p (nerve J) χ)
  let hfinite (n : ℕ) := finiteLift_nonDegenerate p hp J χ n
  let hfree (n : ℕ) := normalizedIntegralChain_free D n
  let hfiniteChains (n : ℕ) := normalizedIntegralChain_finite D n
  let : QuasiIso c := (normalizedSingularComparison_quasiIso_iff _).mpr hcomparison
  let e (n : ℕ) := asIso (homologyMap c n)
  have hnatural : F ≫ c = c ≫ integralChainsFunctor.map (TopCat.ofHom d) :=
    normalizedSingularComparison_naturality _ _ _ d
      (singularLiftDeck_projection p (nerve J) χ d hd)
  have he (n : ℕ) : homologyMap F n ≫ (e n).hom =
      (e n).hom ≫ homologyMap (integralChainsFunctor.map (TopCat.ofHom d)) n := by
    simpa only [homologyMap_comp, e, asIso_hom] using
      congrArg (fun f => homologyMap f n) hnatural
  let N := max 3 (Fintype.card J)
  have htop : (D.normalizedChainComplex integralCoefficient).d (N + 1) N = 0 := by
    have hz := finiteLift_normalizedChain_isZero p hp J χ (N + 1)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
    exact hz.eq_of_src _ _
  apply compactThree_homologyMap_eq_id_of_finite_model P02 d
    (D.normalizedChainComplex integralCoefficient) F e he N (Nat.le_max_left _ _) htop
  exact singularLiftDeck_alternatingTrace_zero p (nerve J) χ d hd
    (hp.deck_fixedPointFree_of_ne_id d (congrArg DFunLike.coe hd) hid) N




theorem compactThree_deck_piThreeMap_eq_transport_of_liftComparison
    (hcomparison : QuasiIso (SSet.chainComplexMap
      (singularLiftProjection p (nerve J) χ) integralCoefficient.{u}))
    (d : C(E, E)) (hd : p.comp d = p) (x : E) (q : Path x (d x))
    (a : HomotopyGroup.Pi 3 E x) :
    surgeryHomotopyMap (n := 3) d rfl a =
      (m59HigherBasepointTransport E 3).map q a :=
  compactThree_piThreeMap_eq_transport_of_homologyMap_eq_id P02 d x q
    (compactThree_deck_homologyMap_eq_id_of_liftComparison P02 p hp J χ
      hcomparison d hd) a

end PoincareConjecture.Proofs.M59
