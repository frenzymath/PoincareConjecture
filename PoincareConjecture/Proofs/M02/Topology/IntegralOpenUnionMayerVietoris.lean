import PoincareConjecture.Proofs.M02.Topology.IntegralMayerVietorisConnectingClass
import PoincareConjecture.Proofs.M02.Topology.IntegralRelativeChains

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

abbrev integralOpenUnion (U V : Set X) := U ∪ V

abbrev integralOpenUnionLeft (U V : Set X) : Set (integralOpenUnion U V) :=
  (Subtype.val : integralOpenUnion U V → X) ⁻¹' U

abbrev integralOpenUnionRight (U V : Set X) : Set (integralOpenUnion U V) :=
  (Subtype.val : integralOpenUnion U V → X) ⁻¹' V

theorem integralOpenUnionLeft_open (U V : Set X) (hU : IsOpen U) :
    IsOpen (integralOpenUnionLeft U V) :=
  hU.preimage continuous_subtype_val

theorem integralOpenUnionRight_open (U V : Set X) (hV : IsOpen V) :
    IsOpen (integralOpenUnionRight U V) :=
  hV.preimage continuous_subtype_val

omit [TopologicalSpace X] in
theorem integralOpenUnion_cover (U V : Set X) :
    integralOpenUnionLeft U V ∪ integralOpenUnionRight U V = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rcases x.property with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

abbrev integralOpenUnionIntersection (U V : Set X) : Set (integralOpenUnion U V) :=
  integralOpenUnionLeft U V ∩ integralOpenUnionRight U V

def integralOpenUnionChainSequence (U V : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  integralOpenChainSequence (integralOpenUnionLeft U V) (integralOpenUnionRight U V)

theorem integralOpenUnionChainSequence_shortExact
    (U V : Set X) :
    (integralOpenUnionChainSequence U V).ShortExact :=
  integralOpenChainSequence_shortExact
    (integralOpenUnionLeft U V) (integralOpenUnionRight U V)

def integralOpenUnionHomologyIso
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    (integralSmallChainComplex (integralBinaryCover
      (integralOpenUnionLeft U V) (integralOpenUnionRight U V))).homology n ≅
      integralHomology (integralOpenUnion U V) n :=
  integralOpenHomologyIso (integralOpenUnionLeft U V) (integralOpenUnionRight U V)
    (integralOpenUnionLeft_open U V hU) (integralOpenUnionRight_open U V hV)
    (integralOpenUnion_cover U V) n

def integralOpenUnionHomologyConnecting
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    integralHomology (integralOpenUnion U V) (n + 1) ⟶
      integralHomology (integralOpenUnionIntersection U V) n :=
  integralOpenHomologyConnecting
    (integralOpenUnionLeft U V) (integralOpenUnionRight U V)
    (integralOpenUnionLeft_open U V hU) (integralOpenUnionRight_open U V hV)
    (integralOpenUnion_cover U V) n

def integralOpenUnionLeftHomeomorph (U V : Set X) :
    integralOpenUnionLeft U V ≃ₜ U :=
  { toEquiv :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

def integralOpenUnionRightHomeomorph (U V : Set X) :
    integralOpenUnionRight U V ≃ₜ V :=
  { toEquiv :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, Or.inr x.2⟩, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

def integralOpenUnionIntersectionHomeomorph (U V : Set X) :
    integralOpenUnionIntersection U V ≃ₜ ↥(U ∩ V) :=
  { toEquiv :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, Or.inl x.2.1⟩, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

def integralOpenUnionHomologyDifference (U V : Set X) (n : Nat) :
    integralHomology ↥(U ∩ V) n ⟶ integralHomology U n ⊞ integralHomology V n :=
  biprod.lift
    (homologyMap (integralNestedChains (Set.inter_subset_left : U ∩ V ⊆ U)) n)
    (-homologyMap (integralNestedChains (Set.inter_subset_right : U ∩ V ⊆ V)) n)

def integralOpenUnionHomologySum (U V : Set X) (n : Nat) :
    integralHomology U n ⊞ integralHomology V n ⟶ integralHomology ↥(U ∪ V) n :=
  biprod.desc
    (homologyMap (integralNestedChains (Set.subset_union_left : U ⊆ U ∪ V)) n)
    (homologyMap (integralNestedChains (Set.subset_union_right : V ⊆ U ∪ V)) n)

def integralOpenUnionHomologyPairIso (U V : Set X) (n : Nat) :
    (integralChains (integralOpenUnionLeft U V) ⊞
      integralChains (integralOpenUnionRight U V)).homology n ≅
        integralHomology U n ⊞ integralHomology V n where
  hom := biprod.lift
    (homologyMap biprod.fst n ≫
      (integralHomeomorphHomologyIso (integralOpenUnionLeftHomeomorph U V) n).hom)
    (homologyMap biprod.snd n ≫
      (integralHomeomorphHomologyIso (integralOpenUnionRightHomeomorph U V) n).hom)
  inv := biprod.desc
    ((integralHomeomorphHomologyIso (integralOpenUnionLeftHomeomorph U V) n).inv ≫
      homologyMap biprod.inl n)
    ((integralHomeomorphHomologyIso (integralOpenUnionRightHomeomorph U V) n).inv ≫
      homologyMap biprod.inr n)
  hom_inv_id := by
    rw [biprod.lift_desc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add, biprod.total,
      homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [Category.assoc, ← homologyMap_comp_assoc]

theorem integralOpenUnionHomologyLeft_intersection (U V : Set X) (n : Nat) :
    homologyMap (integralNestedChains
      (Set.inter_subset_left : integralOpenUnionIntersection U V ⊆
        integralOpenUnionLeft U V)) n ≫
      (integralHomeomorphHomologyIso (integralOpenUnionLeftHomeomorph U V) n).hom =
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom ≫
      homologyMap (integralNestedChains (Set.inter_subset_left : U ∩ V ⊆ U)) n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n ≫ homologyMap _ n
  rw [← homologyMap_comp, ← homologyMap_comp]
  congr 1
  change integralChainsFunctor.map _ ≫ integralChainsFunctor.map _ =
    integralChainsFunctor.map _ ≫ integralChainsFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem integralOpenUnionHomologyRight_intersection (U V : Set X) (n : Nat) :
    homologyMap (integralNestedChains
      (Set.inter_subset_right : integralOpenUnionIntersection U V ⊆
        integralOpenUnionRight U V)) n ≫
      (integralHomeomorphHomologyIso (integralOpenUnionRightHomeomorph U V) n).hom =
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom ≫
      homologyMap (integralNestedChains (Set.inter_subset_right : U ∩ V ⊆ V)) n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n ≫ homologyMap _ n
  rw [← homologyMap_comp, ← homologyMap_comp]
  congr 1
  change integralChainsFunctor.map _ ≫ integralChainsFunctor.map _ =
    integralChainsFunctor.map _ ≫ integralChainsFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem integralOpenUnionHomologyLeft_union (U V : Set X) (n : Nat) :
    (integralHomeomorphHomologyIso (integralOpenUnionLeftHomeomorph U V) n).hom ≫
      homologyMap (integralNestedChains (Set.subset_union_left : U ⊆ U ∪ V)) n =
    homologyMap (integralSubspaceChains (integralOpenUnionLeft U V)) n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n
  rw [← homologyMap_comp]
  congr 1
  change integralChainsFunctor.map _ ≫ integralChainsFunctor.map _ =
    integralChainsFunctor.map _
  rw [← Functor.map_comp]
  rfl

theorem integralOpenUnionHomologyRight_union (U V : Set X) (n : Nat) :
    (integralHomeomorphHomologyIso (integralOpenUnionRightHomeomorph U V) n).hom ≫
      homologyMap (integralNestedChains (Set.subset_union_right : V ⊆ U ∪ V)) n =
    homologyMap (integralSubspaceChains (integralOpenUnionRight U V)) n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n
  rw [← homologyMap_comp]
  congr 1
  change integralChainsFunctor.map _ ≫ integralChainsFunctor.map _ =
    integralChainsFunctor.map _
  rw [← Functor.map_comp]
  rfl

@[reassoc]
theorem integralOpenUnionHomologyDifference_transport (U V : Set X) (n : Nat) :
    homologyMap (integralOpenDifference
      (integralOpenUnionLeft U V) (integralOpenUnionRight U V)) n ≫
      (integralOpenUnionHomologyPairIso U V n).hom =
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom ≫
      integralOpenUnionHomologyDifference U V n := by
  apply biprod.hom_ext
  · simpa [integralOpenUnionHomologyPairIso, integralOpenUnionHomologyDifference,
      Category.assoc, ← homologyMap_comp_assoc, integralOpenDifference] using
      integralOpenUnionHomologyLeft_intersection U V n
  · simpa [integralOpenUnionHomologyPairIso, integralOpenUnionHomologyDifference,
      Category.assoc, ← homologyMap_comp_assoc, integralOpenDifference,
      homologyMap_neg, Preadditive.neg_comp, Preadditive.comp_neg] using
      congrArg Neg.neg (integralOpenUnionHomologyRight_intersection U V n)

@[reassoc]
theorem integralOpenUnionHomologySum_transport
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    (integralOpenUnionHomologyPairIso U V n).hom ≫
      integralOpenUnionHomologySum U V n =
    homologyMap (integralOpenSum
      (integralOpenUnionLeft U V) (integralOpenUnionRight U V)) n ≫
      (integralOpenUnionHomologyIso U V hU hV n).hom := by
  change _ = homologyMap _ n ≫ homologyMap _ n
  rw [← homologyMap_comp, integralOpenSum_inclusion]
  change biprod.lift _ _ ≫ biprod.desc _ _ = _
  rw [biprod.lift_desc, Category.assoc, Category.assoc,
    integralOpenUnionHomologyLeft_union, integralOpenUnionHomologyRight_union,
    ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add]
  congr 1
  apply biprod.hom_ext' <;> simp [Preadditive.comp_add]

def integralOpenUnionHomologyConnectingToIntersection
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    integralHomology (integralOpenUnion U V) (n + 1) ⟶ integralHomology ↥(U ∩ V) n :=
  integralOpenUnionHomologyConnecting U V hU hV n ≫
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom

@[reassoc (attr := simp)]
theorem integralOpenUnionHomologyConnecting_transport
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    (integralOpenUnionHomologyIso U V hU hV (n + 1)).hom ≫
      integralOpenUnionHomologyConnectingToIntersection U V hU hV n =
    (integralOpenUnionChainSequence_shortExact U V).δ (n + 1) n rfl ≫
      (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom := by
  change (integralOpenUnionHomologyIso U V hU hV (n + 1)).hom ≫
    ((integralOpenUnionHomologyIso U V hU hV (n + 1)).inv ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫
      (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom)
      (Iso.hom_inv_id_assoc (integralOpenUnionHomologyIso U V hU hV (n + 1)) _))

@[reassoc (attr := simp)]
theorem integralOpenUnionHomologyDifference_sum
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    integralOpenUnionHomologyDifference U V n ≫
      integralOpenUnionHomologySum U V n = 0 := by
  apply (cancel_epi
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom).mp
  rw [← Category.assoc, ← integralOpenUnionHomologyDifference_transport,
    Category.assoc, integralOpenUnionHomologySum_transport U V hU hV, ← Category.assoc,
    ← homologyMap_comp, integralOpenDifference_sum, homologyMap_zero, zero_comp, comp_zero]

@[reassoc (attr := simp)]
theorem integralOpenUnionHomologySum_connecting
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    integralOpenUnionHomologySum U V (n + 1) ≫
      integralOpenUnionHomologyConnectingToIntersection U V hU hV n = 0 := by
  apply (cancel_epi (integralOpenUnionHomologyPairIso U V (n + 1)).hom).mp
  rw [← Category.assoc, integralOpenUnionHomologySum_transport U V hU hV,
    Category.assoc, integralOpenUnionHomologyConnecting_transport]
  erw [← Category.assoc]
  change (homologyMap (integralOpenUnionChainSequence U V).g (n + 1) ≫
    (integralOpenUnionChainSequence_shortExact U V).δ (n + 1) n rfl) ≫ _ = _
  exact (congrArg (fun f => f ≫
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom)
    ((integralOpenUnionChainSequence_shortExact U V).comp_δ (n + 1) n rfl)).trans
      (zero_comp.trans comp_zero.symm)

@[reassoc (attr := simp)]
theorem integralOpenUnionHomologyConnecting_difference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    integralOpenUnionHomologyConnectingToIntersection U V hU hV n ≫
      integralOpenUnionHomologyDifference U V n = 0 := by
  apply (cancel_epi (integralOpenUnionHomologyIso U V hU hV (n + 1)).hom).mp
  rw [← Category.assoc, integralOpenUnionHomologyConnecting_transport]
  erw [Category.assoc, ← integralOpenUnionHomologyDifference_transport, ← Category.assoc]
  change ((integralOpenUnionChainSequence_shortExact U V).δ (n + 1) n rfl ≫
    homologyMap (integralOpenUnionChainSequence U V).f n) ≫ _ = _
  exact (congrArg (fun f => f ≫ (integralOpenUnionHomologyPairIso U V n).hom)
    ((integralOpenUnionChainSequence_shortExact U V).δ_comp (n + 1) n rfl)).trans
      (zero_comp.trans comp_zero.symm)

def integralOpenUnionHomologyMayerVietoris
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    ShortComplex (ModuleCat.{u} Int) :=
  ShortComplex.mk (integralOpenUnionHomologyDifference U V n)
    (integralOpenUnionHomologySum U V n)
    (integralOpenUnionHomologyDifference_sum U V hU hV n)

theorem integralOpenUnionHomologyMayerVietoris_exact
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    (integralOpenUnionHomologyMayerVietoris U V hU hV n).Exact := by
  let S := integralOpenUnionChainSequence U V
  let e : (ShortComplex.mk (homologyMap S.f n) (homologyMap S.g n)
      (by rw [← homologyMap_comp, S.zero, homologyMap_zero])) ≅
      integralOpenUnionHomologyMayerVietoris U V hU hV n :=
    ShortComplex.isoMk
      (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n)
      (integralOpenUnionHomologyPairIso U V n)
      (integralOpenUnionHomologyIso U V hU hV n)
      (integralOpenUnionHomologyDifference_transport U V n).symm
      (integralOpenUnionHomologySum_transport U V hU hV n)
  exact ShortComplex.exact_of_iso e
    ((integralOpenUnionChainSequence_shortExact U V).homology_exact₂ n)

theorem integralOpenUnionHomologyMayerVietoris_exact_union
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    (ShortComplex.mk (integralOpenUnionHomologySum U V (n + 1))
      (integralOpenUnionHomologyConnectingToIntersection U V hU hV n)
      (integralOpenUnionHomologySum_connecting U V hU hV n)).Exact := by
  let hS := integralOpenUnionChainSequence_shortExact U V
  let e := ShortComplex.isoMk
    (integralOpenUnionHomologyPairIso U V (n + 1))
    (integralOpenUnionHomologyIso U V hU hV (n + 1))
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n)
    (S₁ := ShortComplex.mk _ _ (hS.comp_δ (n + 1) n rfl))
    (S₂ := ShortComplex.mk _ _ (integralOpenUnionHomologySum_connecting U V hU hV n))
    (integralOpenUnionHomologySum_transport U V hU hV (n + 1))
    (integralOpenUnionHomologyConnecting_transport U V hU hV n)
  exact ShortComplex.exact_of_iso e (hS.homology_exact₃ (n + 1) n rfl)

theorem integralOpenUnionHomologyMayerVietoris_exact_intersection
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat) :
    (ShortComplex.mk (integralOpenUnionHomologyConnectingToIntersection U V hU hV n)
      (integralOpenUnionHomologyDifference U V n)
      (integralOpenUnionHomologyConnecting_difference U V hU hV n)).Exact := by
  let hS := integralOpenUnionChainSequence_shortExact U V
  let e := ShortComplex.isoMk
    (integralOpenUnionHomologyIso U V hU hV (n + 1))
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n)
    (integralOpenUnionHomologyPairIso U V n)
    (S₁ := ShortComplex.mk _ _ (hS.δ_comp (n + 1) n rfl))
    (S₂ := ShortComplex.mk _ _ (integralOpenUnionHomologyConnecting_difference U V hU hV n))
    (integralOpenUnionHomologyConnecting_transport U V hU hV n)
    (integralOpenUnionHomologyDifference_transport U V n).symm
  exact ShortComplex.exact_of_iso e (hS.homology_exact₁ (n + 1) n rfl)

theorem integralOpenUnionHomologyConnectingToIntersection_class
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat)
    (z : LinearMap.ker
      ((integralSmallChainComplex (integralBinaryCover
        (integralOpenUnionLeft U V) (integralOpenUnionRight U V))).sc'
        (n + 2) (n + 1) n).g.hom)
    (b : (integralChains (integralOpenUnionLeft U V) ⊞
      integralChains (integralOpenUnionRight U V)).X (n + 1))
    (hb : (integralOpenSum (integralOpenUnionLeft U V)
      (integralOpenUnionRight U V)).f (n + 1) b = z.val)
    (a : LinearMap.ker
      ((integralChains (integralOpenUnionIntersection U V)).sc'
        (n + 1) n (n - 1)).g.hom)
    (hboundary : (integralOpenDifference (integralOpenUnionLeft U V)
      (integralOpenUnionRight U V)).f n a.val =
      (integralChains (integralOpenUnionLeft U V) ⊞
        integralChains (integralOpenUnionRight U V)).d (n + 1) n b) :
    integralOpenUnionHomologyConnectingToIntersection U V hU hV n
      (homologyMap (integralSmallChainInclusion (integralBinaryCover
        (integralOpenUnionLeft U V) (integralOpenUnionRight U V))) (n + 1)
        (moduleComplexHomologyClass
          (integralSmallChainComplex (integralBinaryCover
            (integralOpenUnionLeft U V) (integralOpenUnionRight U V)))
          (n + 2) (n + 1) n (by simp) (by simp) z)) =
      (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom
        (moduleComplexHomologyClass
          (integralChains (integralOpenUnionIntersection U V))
          (n + 1) n (n - 1) (by simp) (by cases n <;> simp) a) := by
  exact congrArg
    (integralHomeomorphHomologyIso (integralOpenUnionIntersectionHomeomorph U V) n).hom
    (integralOpenHomologyConnecting_class
      (integralOpenUnionLeft U V) (integralOpenUnionRight U V)
      (integralOpenUnionLeft_open U V hU) (integralOpenUnionRight_open U V hV)
      (integralOpenUnion_cover U V) n z b hb a hboundary)

end PoincareConjecture.Proofs.M02.Topology
