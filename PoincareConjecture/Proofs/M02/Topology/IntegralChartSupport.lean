import PoincareConjecture.Proofs.M02.Topology.IntegralSupportMayerVietoris
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralOpenSupportMap (K U : Set X) :
    integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ) ⟶ integralSupportChains K :=
  integralPairInclusion Kᶜ U

theorem integralOpenSupportMap_homology_isIso
    (K U : Set X) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : Nat) :
    IsIso (homologyMap (integralOpenSupportMap K U) n) := by
  apply integral_open_cover_excision Kᶜ U hK.isOpen_compl hU ?_ n
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_cases hx : x ∈ K
  · exact Or.inr (hKU hx)
  · exact Or.inl hx

def integralOpenSupportHomologyIso
    (K U : Set X) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : Nat) :
    integralRelativeHomology ((Subtype.val : U → X) ⁻¹' Kᶜ) n ≅
      integralSupportHomology K n := by
  let := integralOpenSupportMap_homology_isIso K U hK hU hKU n
  exact asIso (homologyMap (integralOpenSupportMap K U) n)

theorem integralOpenSupportMap_naturality
    {K L : Set X} (hLK : L ⊆ K) (U : Set X) :
    integralOpenSupportMap K U ≫ integralSupportRestriction hLK =
      integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr hLK)) ≫ integralOpenSupportMap L U := by
  apply (cancel_epi (integralRelativeProjection ((Subtype.val : U → X) ⁻¹' Kᶜ))).mp
  rw [← Category.assoc, integralOpenSupportMap, integralPairInclusion_projection,
    Category.assoc, integralSupportRestriction_projection,
    ← Category.assoc, integralRelativeRestriction_projection,
    integralOpenSupportMap, integralPairInclusion_projection]

def integralRelativeHomeomorphIso (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (h : ∀ x, x ∈ A ↔ e x ∈ B) : integralRelativeChains A ≅ integralRelativeChains B :=
  cokernel.mapIso _ _
    (integralChainsFunctor.mapIso (TopCat.isoOfHomeo (e.subtype h)))
    (integralChainsFunctor.mapIso (TopCat.isoOfHomeo e)) (by
      simp only [Functor.mapIso_hom, integralSubspaceChains, ← Functor.map_comp]
      rfl)

@[reassoc (attr := simp)]
theorem integralRelativeHomeomorphIso_projection
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    integralRelativeProjection A ≫ (integralRelativeHomeomorphIso e A B h).hom =
      integralChainsFunctor.map (TopCat.ofHom (e : C(X, Y))) ≫
        integralRelativeProjection B := by
  simp only [integralRelativeHomeomorphIso, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc, Functor.mapIso_hom]
  rfl

theorem integralRelativeHomeomorphIso_naturality
    (e : X ≃ₜ Y) {A A' : Set X} {B B' : Set Y}
    (h : ∀ x, x ∈ A ↔ e x ∈ B) (h' : ∀ x, x ∈ A' ↔ e x ∈ B')
    (hA : A ⊆ A') (hB : B ⊆ B') :
    (integralRelativeHomeomorphIso e A B h).hom ≫ integralRelativeRestriction hB =
      integralRelativeRestriction hA ≫ (integralRelativeHomeomorphIso e A' B' h').hom := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [← Category.assoc, integralRelativeHomeomorphIso_projection,
    Category.assoc, integralRelativeRestriction_projection,
    ← Category.assoc, integralRelativeRestriction_projection,
    integralRelativeHomeomorphIso_projection]

def integralChartRelativeChainsIso (e : OpenPartialHomeomorph X Y)
    (K : Set X) (hK : K ⊆ e.source) :
    integralRelativeChains ((Subtype.val : e.source → X) ⁻¹' Kᶜ) ≅
      integralRelativeChains ((Subtype.val : e.target → Y) ⁻¹' (e '' K)ᶜ) :=
  integralRelativeHomeomorphIso e.toHomeomorphSourceTarget _ _ (by
    intro p
    change p.val ∉ K ↔ e p.val ∉ e '' K
    constructor
    · intro hp he
      obtain ⟨k, hk, hkp⟩ := he
      exact hp ((e.injOn (hK hk) p.property hkp) ▸ hk)
    · intro hp hk
      exact hp ⟨p.val, hk, rfl⟩)

@[reassoc (attr := simp)]
theorem integralChartRelativeChainsIso_projection
    (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : K ⊆ e.source) :
    integralRelativeProjection ((Subtype.val : e.source → X) ⁻¹' Kᶜ) ≫
      (integralChartRelativeChainsIso e K hK).hom =
        integralChainsFunctor.map (TopCat.ofHom
          (e.toHomeomorphSourceTarget : C(e.source, e.target))) ≫
            integralRelativeProjection ((Subtype.val : e.target → Y) ⁻¹' (e '' K)ᶜ) :=
  integralRelativeHomeomorphIso_projection _ _ _ _

theorem integralChartRelativeChainsIso_naturality
    (e : OpenPartialHomeomorph X Y) {K L : Set X}
    (hK : K ⊆ e.source) (hL : L ⊆ e.source) (hLK : L ⊆ K) :
    (integralChartRelativeChainsIso e K hK).hom ≫
        integralRelativeRestriction
          (Set.preimage_mono (Set.compl_subset_compl.mpr (Set.image_mono hLK))) =
      integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr hLK)) ≫
          (integralChartRelativeChainsIso e L hL).hom :=
  integralRelativeHomeomorphIso_naturality _ _ _ _ _

def integralChartSupportHomologyIso [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (n : Nat) :
    integralSupportHomology K n ≅ integralSupportHomology (e '' K) n :=
  (integralOpenSupportHomologyIso K e.source hK.isClosed e.open_source hKs n).symm ≪≫
    (homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).mapIso
      (integralChartRelativeChainsIso e K hKs) ≪≫
    integralOpenSupportHomologyIso (e '' K) e.target
      (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed e.open_target
      (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)) n

theorem integralChartSupportHomologyIso_naturality [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKs : K ⊆ e.source)
    (hLs : L ⊆ e.source) (hLK : L ⊆ K) (n : Nat) :
    (integralChartSupportHomologyIso e K hK hKs n).hom ≫
        integralSupportHomologyRestriction (Set.image_mono hLK) n =
      integralSupportHomologyRestriction hLK n ≫
        (integralChartSupportHomologyIso e L hL hLs n).hom := by
  let SK := integralOpenSupportHomologyIso K e.source hK.isClosed e.open_source hKs n
  let SL := integralOpenSupportHomologyIso L e.source hL.isClosed e.open_source hLs n
  let TK := integralOpenSupportHomologyIso (e '' K) e.target
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)) n
  let TL := integralOpenSupportHomologyIso (e '' L) e.target
    (hL.image_of_continuousOn (e.continuousOn.mono hLs)).isClosed e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hLs hx)) n
  let f := homologyMap (integralChartRelativeChainsIso e K hKs).hom n
  let g := homologyMap (integralChartRelativeChainsIso e L hLs).hom n
  let r := homologyMap (integralRelativeRestriction
    (Set.preimage_mono (f := (Subtype.val : e.source → X))
      (Set.compl_subset_compl.mpr hLK))) n
  let s := homologyMap (integralRelativeRestriction
    (Set.preimage_mono (f := (Subtype.val : e.target → Y))
      (Set.compl_subset_compl.mpr (Set.image_mono (f := e) hLK)))) n
  have hS : SK.hom ≫ integralSupportHomologyRestriction hLK n = r ≫ SL.hom := by
    change homologyMap (integralOpenSupportMap K e.source) n ≫
        homologyMap (integralSupportRestriction hLK) n =
      homologyMap (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr hLK))) n ≫
        homologyMap (integralOpenSupportMap L e.source) n
    rw [← homologyMap_comp, ← homologyMap_comp, integralOpenSupportMap_naturality]
  have hT : TK.hom ≫ integralSupportHomologyRestriction (Set.image_mono hLK) n =
      s ≫ TL.hom := by
    change homologyMap (integralOpenSupportMap (e '' K) e.target) n ≫
        homologyMap (integralSupportRestriction (Set.image_mono hLK)) n =
      homologyMap (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr (Set.image_mono hLK)))) n ≫
        homologyMap (integralOpenSupportMap (e '' L) e.target) n
    rw [← homologyMap_comp, ← homologyMap_comp, integralOpenSupportMap_naturality]
  have hchart : f ≫ s = r ≫ g := by
    dsimp only [f, g, s, r]
    rw [← homologyMap_comp, ← homologyMap_comp,
      integralChartRelativeChainsIso_naturality e hKs hLs hLK]
  change (SK.inv ≫ f ≫ TK.hom) ≫ _ = _ ≫ (SL.inv ≫ g ≫ TL.hom)
  apply (cancel_epi SK.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc SK.hom, hS]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hT, ← Category.assoc f, hchart, Category.assoc]

end PoincareConjecture.Proofs.M02.Topology
