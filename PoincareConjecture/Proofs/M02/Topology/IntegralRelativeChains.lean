import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Module.ULift
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Homotopy.Contractible









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial BigOperators unitInterval

universe u

namespace PoincareConjecture.Proofs.M02.Topology

abbrev integralCoefficient : ModuleCat.{u} Int :=
  ModuleCat.of Int (ULift.{u} Int)

abbrev integralChainsFunctor :
    TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} Int) Nat :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} Int)).obj
    integralCoefficient

abbrev integralChains (X : Type u) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  integralChainsFunctor.obj (TopCat.of X)

abbrev integralHomology (X : Type u) [TopologicalSpace X] (n : Nat) :
    ModuleCat.{u} Int :=
  (integralChains X).homology n

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSubspaceChains (A : Set X) : integralChains A ⟶ integralChains X :=
  integralChainsFunctor.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

theorem integralSubspaceChains_mono (A : Set X) : Mono (integralSubspaceChains A) := by
  let i : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  change Mono (integralChainsFunctor.map i)
  infer_instance

abbrev integralRelativeChains (A : Set X) : ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralSubspaceChains A)

abbrev integralRelativeHomology (A : Set X) (n : Nat) : ModuleCat.{u} Int :=
  (integralRelativeChains A).homology n

abbrev integralRelativeProjection (A : Set X) :
    integralChains X ⟶ integralRelativeChains A :=
  cokernel.π (integralSubspaceChains A)

abbrev integralToRelativeHomology (A : Set X) (n : Nat) :
    integralHomology X n ⟶ integralRelativeHomology A n :=
  HomologicalComplex.homologyMap (integralRelativeProjection A) n

def integralRelativeMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) : integralRelativeChains A ⟶ integralRelativeChains B :=
  cokernel.map (integralSubspaceChains A) (integralSubspaceChains B)
    (integralChainsFunctor.map (TopCat.ofHom
      ⟨fun a : A => ⟨f a, hf a.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩))
    (integralChainsFunctor.map (TopCat.ofHom f)) (by
      simp only [integralSubspaceChains, ← Functor.map_comp]
      rfl)

theorem integralRelativeMap_projection (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) :
    integralRelativeProjection A ≫ integralRelativeMap f hf =
      integralChainsFunctor.map (TopCat.ofHom f) ≫ integralRelativeProjection B :=
  cokernel.π_desc _ _ _

abbrev integralPairSequence (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.cokernelSequence (integralSubspaceChains A)

theorem integralPairSequence_shortExact (A : Set X) :
    (integralPairSequence A).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (integralSubspaceChains A)
  mono_f := integralSubspaceChains_mono A

def integralRelativeBoundary (A : Set X) (n : Nat) :
    integralRelativeHomology A (n + 1) ⟶ integralHomology A n :=
  (integralPairSequence_shortExact A).δ (n + 1) n rfl

theorem integral_relative_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Nonempty (Homotopy (integralRelativeMap f hf) (integralRelativeMap g hg)) := by
  let ia : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let ib : TopCat.of B ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let fa : C(A, B) := ⟨fun a => ⟨f a, hf a.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let ga : C(A, B) := ⟨fun a => ⟨g a, hg a.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let HA : ContinuousMap.Homotopy fa ga :=
    { toFun := fun q => ⟨H (q.1, q.2), hH q.1 q.2.property⟩
      continuous_toFun :=
        (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left a := Subtype.ext (H.map_zero_left a)
      map_one_left a := Subtype.ext (H.map_one_left a) }
  let HT : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  let HAT : TopCat.Homotopy (TopCat.ofHom fa) (TopCat.ofHom ga) := HA
  have htop : ia ▷ TopCat.I ≫ HT.h = HAT.h ≫ ib := by
    ext q
    rfl
  have hs : TopCat.toSSet.map ia ▷ Δ[1] ≫ HT.toSSet.h =
      HAT.toSSet.h ≫ TopCat.toSSet.map ib := by
    dsimp [TopCat.Homotopy.toSSet]
    rw [← whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← TopCat.toSSet.map_comp, htop, TopCat.toSSet.map_comp]
    simp only [Category.assoc]
  let S := HT.toSSet.toSimplicialObjectHomotopy
  let SA := HAT.toSSet.toSimplicialObjectHomotopy
  have hsimplex (n : Nat) (k : Fin (n + 1)) :
      (TopCat.toSSet.map ia).app (Opposite.op ⦋n⦌) ≫ S.h k =
        SA.h k ≫ (TopCat.toSSet.map ib).app (Opposite.op ⦋n + 1⦌) := by
    ext x
    change ((SSet.yonedaEquiv.symm ((TopCat.toSSet.map ia).app _ x) ▷ Δ[1]) ≫
        HT.toSSet.h).app _ _ =
      ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ≫ HAT.toSSet.h ≫
        TopCat.toSSet.map ib).app _ _
    rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, hs]
  let F : Type u ⥤ ModuleCat.{u} Int := sigmaConst.obj integralCoefficient
  let P : Homotopy (integralChainsFunctor.map (TopCat.ofHom f))
      (integralChainsFunctor.map (TopCat.ofHom g)) :=
    HT.singularChainComplexFunctorObjMap integralCoefficient
  let PA : Homotopy (integralChainsFunctor.map (TopCat.ofHom fa))
      (integralChainsFunctor.map (TopCat.ofHom ga)) :=
    HAT.singularChainComplexFunctorObjMap integralCoefficient
  have hprism (i j : Nat) :
      (integralSubspaceChains A).f i ≫ P.hom i j =
        PA.hom i j ≫ (integralSubspaceChains B).f j := by
    by_cases hij : i + 1 = j
    · subst j
      change F.map ((TopCat.toSSet.map ia).app (Opposite.op ⦋i⦌)) ≫
          CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
            (S.whiskerRight F) i (i + 1) =
        CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
            (SA.whiskerRight F) i (i + 1) ≫
          F.map ((TopCat.toSSet.map ib).app (Opposite.op ⦋i + 1⦌))
      rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
        CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
      change F.map ((TopCat.toSSet.map ia).app (Opposite.op ⦋i⦌)) ≫
          (-∑ k : Fin (i + 1), ((-1 : Int) ^ k.val) • F.map (S.h k)) =
        (-∑ k : Fin (i + 1), ((-1 : Int) ^ k.val) • F.map (SA.h k)) ≫
          F.map ((TopCat.toSSet.map ib).app (Opposite.op ⦋i + 1⦌))
      simp only [Preadditive.comp_neg, Preadditive.neg_comp,
        Preadditive.comp_sum, Preadditive.sum_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      rw [← F.map_comp, ← F.map_comp, hsimplex]
    · rw [P.zero i j hij, PA.zero i j hij, comp_zero, zero_comp]
  let pA := integralRelativeProjection A
  let pB := integralRelativeProjection B
  have hzero (i j : Nat) :
      (integralSubspaceChains A).f i ≫ (P.hom i j ≫ pB.f j) = 0 := by
    rw [← Category.assoc, hprism, Category.assoc]
    have hb : (integralSubspaceChains B).f j ≫ pB.f j = 0 :=
      congrArg (fun q => q.f j) (cokernel.condition (integralSubspaceChains B))
    rw [hb, comp_zero]
  let D (i j : Nat) :=
    CokernelCofork.IsColimit.desc'
      (isColimitOfHasCokernelOfPreservesColimit
        (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) i)
        (integralSubspaceChains A))
      (P.hom i j ≫ pB.f j) (hzero i j)
  let T (i j : Nat) : (integralRelativeChains A).X i ⟶
      (integralRelativeChains B).X j := (D i j).val
  have hT (i j : Nat) : pA.f i ≫ T i j = P.hom i j ≫ pB.f j := (D i j).property
  have hf' (i : Nat) : pA.f i ≫ (integralRelativeMap f hf).f i =
      (integralChainsFunctor.map (TopCat.ofHom f)).f i ≫ pB.f i :=
    congrArg (fun q => q.f i) (integralRelativeMap_projection f hf)
  have hg' (i : Nat) : pA.f i ≫ (integralRelativeMap g hg).f i =
      (integralChainsFunctor.map (TopCat.ofHom g)).f i ≫ pB.f i :=
    congrArg (fun q => q.f i) (integralRelativeMap_projection g hg)
  refine ⟨{ hom := T, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    apply (cancel_epi (pA.f i)).mp
    rw [hT, P.zero i j hij, zero_comp, comp_zero]
  · intro i
    apply (cancel_epi (pA.f i)).mp
    rw [Preadditive.comp_add, Preadditive.comp_add, hf', hg',
      ← dNext_comp_left pA T i, ← prevD_comp_left pA T i]
    simp_rw [hT]
    rw [dNext_comp_right P.hom pB i, prevD_comp_right P.hom pB i, P.comm i]
    simp only [Preadditive.add_comp]

def integralHomeomorphHomologyIso (e : X ≃ₜ Y) (n : Nat) :
    integralHomology X n ≅ integralHomology Y n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).mapIso
    (integralChainsFunctor.mapIso (TopCat.isoOfHomeo e))

theorem integral_contractible_homology_isZero
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : Nat) (hn : n ≠ 0) : IsZero (integralHomology X n) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let a : TopCat.of X ⟶ TopCat.of (ULift.{u} Unit) :=
    TopCat.ofHom (ContinuousMap.const X (ULift.up ()))
  let b : TopCat.of (ULift.{u} Unit) ⟶ TopCat.of X :=
    TopCat.ofHom (ContinuousMap.const (ULift.{u} Unit) x)
  have hz : IsZero (integralHomology (ULift.{u} Unit) n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} Int) n integralCoefficient (TopCat.of (ULift.{u} Unit)) hn
  have H' : TopCat.Homotopy (𝟙 (TopCat.of X)) (a ≫ b) := H
  have heq := H'.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  rw [IsZero.iff_id_eq_zero]
  have hmap : HomologicalComplex.homologyMap (integralChainsFunctor.map (a ≫ b)) n = 0 := by
    rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
    rw [hz.eq_of_tgt (HomologicalComplex.homologyMap (integralChainsFunctor.map a) n) 0,
      zero_comp]
  have hid : HomologicalComplex.homologyMap
      (integralChainsFunctor.map (𝟙 (TopCat.of X))) n = 0 := heq.trans hmap
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at hid
  exact hid

end PoincareConjecture.Proofs.M02.Topology
