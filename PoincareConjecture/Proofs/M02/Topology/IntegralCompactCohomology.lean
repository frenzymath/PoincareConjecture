import PoincareConjecture.Proofs.M02.Topology.IntegralDualBiprod
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportMayerVietoris
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportUniv
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.Topology.Sets.Compacts









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

@[simp]
theorem integralRelativeRestriction_refl (A : Set X) :
    integralRelativeRestriction (Set.Subset.refl A) = 𝟙 (integralRelativeChains A) := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [integralRelativeRestriction_projection, Category.comp_id]

@[simp]
theorem integralSupportCohomologyPushforward_refl (K : Set X) (q : Nat) :
    integralSupportCohomologyPushforward (Set.Subset.refl K) q =
      𝟙 (integralSupportCohomology K q) := by
  change homologyMap (integralDualMap (integralRelativeRestriction
    (Set.Subset.refl Kᶜ))) q = _
  rw [integralRelativeRestriction_refl, integralDualMap_id, homologyMap_id]

@[reassoc (attr := simp)]
theorem integralSupportCohomologyPushforward_comp {K L P : Set X}
    (hKL : K ⊆ L) (hLP : L ⊆ P) (q : Nat) :
    integralSupportCohomologyPushforward hKL q ≫
        integralSupportCohomologyPushforward hLP q =
      integralSupportCohomologyPushforward (hKL.trans hLP) q := by
  change homologyMap (integralDualMap (integralSupportRestriction hKL)) q ≫
      homologyMap (integralDualMap (integralSupportRestriction hLP)) q =
    homologyMap (integralDualMap (integralSupportRestriction (hKL.trans hLP))) q
  rw [← homologyMap_comp, ← integralDualMap_comp, integralSupportRestriction_comp]

def integralCompactSupportCohomologyFunctor (X : Type u) [TopologicalSpace X] (q : Nat) :
    Compacts X ⥤ ModuleCat.{u} Int where
  obj K := integralSupportCohomology (K : Set X) q
  map f := integralSupportCohomologyPushforward (leOfHom f) q
  map_id K := integralSupportCohomologyPushforward_refl (K : Set X) q
  map_comp f g := (integralSupportCohomologyPushforward_comp (leOfHom f) (leOfHom g) q).symm

def integralCompactSupportCohomology (X : Type u) [TopologicalSpace X] (q : Nat) :
    ModuleCat.{u} Int :=
  colimit (integralCompactSupportCohomologyFunctor X q)

def integralCompactSupportCohomologyClass (K : Compacts X) (q : Nat) :
    integralSupportCohomology (K : Set X) q ⟶ integralCompactSupportCohomology X q :=
  colimit.ι (integralCompactSupportCohomologyFunctor X q) K

@[reassoc (attr := simp)]
theorem integralCompactSupportCohomologyClass_pushforward
    {K L : Compacts X} (h : K ≤ L) (q : Nat) :
    integralSupportCohomologyPushforward h q ≫ integralCompactSupportCohomologyClass L q =
      integralCompactSupportCohomologyClass K q :=
  colimit.w (integralCompactSupportCohomologyFunctor X q) (homOfLE h)

theorem exists_integralCompactSupportCohomology_representative (q : Nat)
    (a : integralCompactSupportCohomology X q) :
    ∃ (K : Compacts X) (b : integralSupportCohomology (K : Set X) q),
      integralCompactSupportCohomologyClass K q b = a := by
  let F := integralCompactSupportCohomologyFunctor X q
  let h := ModuleCat.FilteredColimits.colimitCoconeIsColimit F
  let e := h.coconePointUniqueUpToIso (colimit.isColimit F)
  obtain ⟨K, b, hb⟩ := ModuleCat.FilteredColimits.M.mk_surjective F (e.inv a)
  refine ⟨K, b, ?_⟩
  have he := congrArg (fun f => f b)
    (IsColimit.comp_coconePointUniqueUpToIso_hom h (colimit.isColimit F) K)
  change e.hom (ModuleCat.FilteredColimits.M.mk F ⟨K, b⟩) =
    integralCompactSupportCohomologyClass K q b at he
  rw [hb] at he
  refine he.symm.trans ?_
  change (e.inv ≫ e.hom) a = a
  rw [e.inv_hom_id]
  rfl

theorem integralCompactSupportCohomology_induction (q : Nat)
    (P : integralCompactSupportCohomology X q → Prop)
    (h : ∀ (K : Compacts X) (b : integralSupportCohomology (K : Set X) q),
      P (integralCompactSupportCohomologyClass K q b))
    (a : integralCompactSupportCohomology X q) : P a := by
  obtain ⟨K, b, rfl⟩ := exists_integralCompactSupportCohomology_representative q a
  exact h K b

theorem integralCompactSupportCohomology_hom_ext (q : Nat) {V : ModuleCat.{u} Int}
    {f g : integralCompactSupportCohomology X q ⟶ V}
    (h : ∀ K : Compacts X, integralCompactSupportCohomologyClass K q ≫ f =
      integralCompactSupportCohomologyClass K q ≫ g) : f = g :=
  colimit.hom_ext h

def integralCompactSupportCohomologyDesc (q : Nat) (V : ModuleCat.{u} Int)
    (f : ∀ K : Compacts X, integralSupportCohomology (K : Set X) q ⟶ V)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L), integralSupportCohomologyPushforward h q ≫
      f L = f K) : integralCompactSupportCohomology X q ⟶ V :=
  colimit.desc (integralCompactSupportCohomologyFunctor X q)
    { pt := V
      ι := { app := f
             naturality := by
               intro K L h
               exact (hf K L (leOfHom h)).trans (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
theorem integralCompactSupportCohomologyClass_desc (q : Nat) (V : ModuleCat.{u} Int)
    (f : ∀ K : Compacts X, integralSupportCohomology (K : Set X) q ⟶ V)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L), integralSupportCohomologyPushforward h q ≫
      f L = f K) (K : Compacts X) :
    integralCompactSupportCohomologyClass K q ≫ integralCompactSupportCohomologyDesc q V f hf =
      f K :=
  colimit.ι_desc _ K

def integralCompactSupportCohomologyTopIso [CompactSpace X] (q : Nat) :
    integralCompactSupportCohomology X q ≅ integralSupportCohomology (Set.univ : Set X) q :=
  (colimit.isColimit (integralCompactSupportCohomologyFunctor X q)).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (isTerminalTop (α := Compacts X))
      (integralCompactSupportCohomologyFunctor X q))

@[reassoc (attr := simp)]
theorem integralCompactSupportCohomologyTopIso_class [CompactSpace X]
    (q : Nat) (K : Compacts X) :
    integralCompactSupportCohomologyClass K q ≫ (integralCompactSupportCohomologyTopIso q).hom =
      integralSupportCohomologyPushforward (Set.subset_univ (K : Set X)) q := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (integralCompactSupportCohomologyFunctor X q))
    (colimitOfDiagramTerminal (isTerminalTop (α := Compacts X))
      (integralCompactSupportCohomologyFunctor X q)) K

def integralDualIso {C D : ChainComplex (ModuleCat.{u} Int) Nat} (e : C ≅ D) :
    integralDualComplex D ≅ integralDualComplex C where
  hom := integralDualMap e.hom
  inv := integralDualMap e.inv
  hom_inv_id := by rw [← integralDualMap_comp, e.inv_hom_id, integralDualMap_id]
  inv_hom_id := by rw [← integralDualMap_comp, e.hom_inv_id, integralDualMap_id]

def integralCohomologyForgetSupport (K : Set X) (q : Nat) :
    integralSupportCohomology K q ⟶ integralCohomology X q :=
  homologyMap (integralDualMap (integralRelativeProjection Kᶜ)) q

@[reassoc (attr := simp)]
theorem integralCohomologyForgetSupport_pushforward {K L : Set X}
    (h : K ⊆ L) (q : Nat) :
    integralSupportCohomologyPushforward h q ≫ integralCohomologyForgetSupport L q =
      integralCohomologyForgetSupport K q := by
  change homologyMap (integralDualMap (integralSupportRestriction h)) q ≫
      homologyMap (integralDualMap (integralRelativeProjection Lᶜ)) q = _
  rw [← homologyMap_comp, ← integralDualMap_comp]
  change homologyMap (integralDualMap
    (integralRelativeProjection Lᶜ ≫ integralRelativeRestriction
      (Set.compl_subset_compl.mpr h))) q = _
  rw [integralRelativeRestriction_projection]
  rfl

theorem integralCohomologyForgetSupport_univ_isIso (q : Nat) :
    IsIso (integralCohomologyForgetSupport (Set.univ : Set X) q) := by
  let := integralRelativeProjection_empty_isIso (X := X)
  change IsIso (homologyMap (integralDualMap
    (integralRelativeProjection (Set.univ : Set X)ᶜ)) q)
  rw [Set.compl_univ]
  let e := integralDualIso (asIso (integralRelativeProjection (∅ : Set X)))
  change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.up Nat) q).map e.hom)
  infer_instance

def integralCompactSupportCohomologyIso [CompactSpace X] (q : Nat) :
    integralCompactSupportCohomology X q ≅ integralCohomology X q :=
  letI := integralCohomologyForgetSupport_univ_isIso (X := X) q
  integralCompactSupportCohomologyTopIso q ≪≫
    asIso (integralCohomologyForgetSupport (Set.univ : Set X) q)

@[reassoc (attr := simp)]
theorem integralCompactSupportCohomologyIso_class [CompactSpace X]
    (q : Nat) (K : Compacts X) :
    integralCompactSupportCohomologyClass K q ≫ (integralCompactSupportCohomologyIso q).hom =
      integralCohomologyForgetSupport (K : Set X) q := by
  simp [integralCompactSupportCohomologyIso]

theorem integralCompactSupportCohomologyClass_eq_iff
    {q : Nat} {K L : Compacts X} (a : integralSupportCohomology (K : Set X) q)
    (b : integralSupportCohomology (L : Set X) q) :
    integralCompactSupportCohomologyClass K q a =
        integralCompactSupportCohomologyClass L q b ↔
      ∃ (P : Compacts X) (hKP : K ≤ P) (hLP : L ≤ P),
        integralSupportCohomologyPushforward hKP q a =
          integralSupportCohomologyPushforward hLP q b := by
  let F := integralCompactSupportCohomologyFunctor X q
  let h := ModuleCat.FilteredColimits.colimitCoconeIsColimit F
  let e := h.coconePointUniqueUpToIso (colimit.isColimit F)
  change F.obj K at a
  change F.obj L at b
  have he (P : Compacts X) (c : F.obj P) :
      e.hom (ModuleCat.FilteredColimits.M.mk F ⟨P, c⟩) =
        integralCompactSupportCohomologyClass P q c :=
    congrArg (fun f => f c)
      (IsColimit.comp_coconePointUniqueUpToIso_hom h (colimit.isColimit F) P)
  have hinj := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have h1 :
      integralCompactSupportCohomologyClass K q a =
          integralCompactSupportCohomologyClass L q b ↔
        e.hom (ModuleCat.FilteredColimits.M.mk F ⟨K, a⟩) =
          e.hom (ModuleCat.FilteredColimits.M.mk F ⟨L, b⟩) := by
    constructor
    · intro hEq
      exact (he K a).trans (hEq.trans (he L b).symm)
    · intro hEq
      exact (he K a).symm.trans (hEq.trans (he L b))
  refine h1.trans (hinj.eq_iff.trans ?_)
  change (F ⋙ forget (ModuleCat.{u} Int)).ιColimitType K a =
      (F ⋙ forget (ModuleCat.{u} Int)).ιColimitType L b ↔ _
  rw [Functor.ιColimitType_eq_iff_of_isFiltered]
  constructor
  · rintro ⟨P, f, g, hfg⟩
    exact ⟨P, leOfHom f, leOfHom g, hfg⟩
  · rintro ⟨P, hKP, hLP, hfg⟩
    exact ⟨P, homOfLE hKP, homOfLE hLP, hfg⟩

@[simp] theorem integralCompactSupportCohomologyClass_bot_eq_zero (q : Nat) :
    integralCompactSupportCohomologyClass (⊥ : Compacts X) q 0 = 0 := by
  simp [integralCompactSupportCohomologyClass]

theorem integralCompactSupportCohomologyClass_eq_zero_iff
    {q : Nat} {K : Compacts X} (a : integralSupportCohomology (K : Set X) q) :
    integralCompactSupportCohomologyClass K q a = 0 ↔
      ∃ (P : Compacts X) (hKP : K ≤ P),
        integralSupportCohomologyPushforward hKP q a = 0 := by
  rw [← integralCompactSupportCohomologyClass_bot_eq_zero (X := X) q]
  constructor
  · intro h
    obtain ⟨P, hKP, hbot, hEq⟩ :=
      (integralCompactSupportCohomologyClass_eq_iff a
        (0 : integralSupportCohomology ((⊥ : Compacts X) : Set X) q)).mp h
    exact ⟨P, hKP, by simpa using hEq⟩
  · rintro ⟨P, hKP, hzero⟩
    apply (integralCompactSupportCohomologyClass_eq_iff a
      (0 : integralSupportCohomology ((⊥ : Compacts X) : Set X) q)).mpr
    exact ⟨P, hKP, bot_le, by simpa using hzero⟩

end PoincareConjecture.Proofs.M02.Topology
