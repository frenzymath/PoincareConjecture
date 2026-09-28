import PoincareConjecture.Proofs.M02.Topology.IntegralChainUniverse
import PoincareConjecture.Proofs.M02.Topology.ModuleComplexUniverse
import PoincareConjecture.Proofs.M02.Topology.IntegralChartSupport









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def integralHomeomorphHomologyEquiv (e : X ≃ₜ Y) (n : Nat) :
    integralHomology X n ≃ₗ[Int] integralHomology Y n :=
  moduleComplexHomologyEquiv (integralChains X) (integralChains Y)
    (integralChainHomeomorphEquiv e) (integralChainHomeomorphEquiv_d e) n

def integralRelativeHomeomorphHomologyEquiv (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : Nat) :
    integralRelativeHomology A n ≃ₗ[Int] integralRelativeHomology B n :=
  moduleComplexHomologyEquiv (integralRelativeChains A) (integralRelativeChains B)
    (integralRelativeHomeomorphEquiv e A B h)
    (integralRelativeHomeomorphEquiv_d e A B h) n

theorem integralRelativeHomeomorphHomologyEquiv_naturality (e : X ≃ₜ Y)
    {A A' : Set X} {B B' : Set Y}
    (h : ∀ x, x ∈ A ↔ e x ∈ B) (h' : ∀ x, x ∈ A' ↔ e x ∈ B')
    (hA : A ⊆ A') (hB : B ⊆ B') (n : Nat) (a : integralRelativeHomology A n) :
    integralRelativeHomeomorphHomologyEquiv e A' B' h' n
        (homologyMap (integralRelativeRestriction hA) n a) =
      homologyMap (integralRelativeRestriction hB) n
        (integralRelativeHomeomorphHomologyEquiv e A B h n a) :=
  moduleComplexHomologyEquiv_naturality _ _ _ _
    (integralRelativeRestriction hA) (integralRelativeRestriction hB)
    (fun n c => (integralRelativeHomeomorphEquiv_naturality e h h' hA hB n c).symm) n a

def integralChartRelativeHomologyEquiv (e : OpenPartialHomeomorph X Y)
    (K : Set X) (hK : K ⊆ e.source) (n : Nat) :
    integralRelativeHomology ((Subtype.val : e.source → X) ⁻¹' Kᶜ) n ≃ₗ[Int]
      integralRelativeHomology ((Subtype.val : e.target → Y) ⁻¹' (e '' K)ᶜ) n :=
  integralRelativeHomeomorphHomologyEquiv e.toHomeomorphSourceTarget _ _ (by
    intro p
    change p.val ∉ K ↔ e p.val ∉ e '' K
    constructor
    · intro hp he
      obtain ⟨k, hk, hkp⟩ := he
      exact hp ((e.injOn (hK hk) p.property hkp) ▸ hk)
    · intro hp hk
      exact hp ⟨p.val, hk, rfl⟩) n

theorem integralChartRelativeHomologyEquiv_naturality (e : OpenPartialHomeomorph X Y)
    {K L : Set X} (hK : K ⊆ e.source) (hL : L ⊆ e.source) (hLK : L ⊆ K)
    (n : Nat) (a : integralRelativeHomology ((Subtype.val : e.source → X) ⁻¹' Kᶜ) n) :
    integralChartRelativeHomologyEquiv e L hL n
        (homologyMap (integralRelativeRestriction
          (Set.preimage_mono (Set.compl_subset_compl.mpr hLK))) n a) =
      homologyMap (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr (Set.image_mono hLK)))) n
          (integralChartRelativeHomologyEquiv e K hK n a) :=
  integralRelativeHomeomorphHomologyEquiv_naturality _ _ _ _ _ n a

def integralChartSupportHomologyEquiv [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (n : Nat) :
    integralSupportHomology K n ≃ₗ[Int] integralSupportHomology (e '' K) n :=
  (integralOpenSupportHomologyIso K e.source hK.isClosed e.open_source hKs
    n).toLinearEquiv.symm.trans
    ((integralChartRelativeHomologyEquiv e K hKs n).trans
      (integralOpenSupportHomologyIso (e '' K) e.target
        (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed e.open_target
        (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)) n).toLinearEquiv)

theorem integralChartSupportHomologyEquiv_naturality [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKs : K ⊆ e.source)
    (hLs : L ⊆ e.source) (hLK : L ⊆ K) (n : Nat) (a : integralSupportHomology K n) :
    integralChartSupportHomologyEquiv e L hL hLs n
        (integralSupportHomologyRestriction hLK n a) =
      integralSupportHomologyRestriction (Set.image_mono hLK) n
        (integralChartSupportHomologyEquiv e K hK hKs n a) := by
  let SK := (integralOpenSupportHomologyIso K e.source hK.isClosed e.open_source hKs
    n).toLinearEquiv
  let SL := (integralOpenSupportHomologyIso L e.source hL.isClosed e.open_source hLs
    n).toLinearEquiv
  let TK := (integralOpenSupportHomologyIso (e '' K) e.target
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)) n).toLinearEquiv
  let TL := (integralOpenSupportHomologyIso (e '' L) e.target
    (hL.image_of_continuousOn (e.continuousOn.mono hLs)).isClosed e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hLs hx)) n).toLinearEquiv
  let r := homologyMap (integralRelativeRestriction
    (Set.preimage_mono (f := (Subtype.val : e.source → X))
      (Set.compl_subset_compl.mpr hLK))) n
  let s := homologyMap (integralRelativeRestriction
    (Set.preimage_mono (f := (Subtype.val : e.target → Y))
      (Set.compl_subset_compl.mpr (Set.image_mono (f := e) hLK)))) n
  have hS (z : integralRelativeHomology ((Subtype.val : e.source → X) ⁻¹' Kᶜ) n) :
      integralSupportHomologyRestriction hLK n (SK z) = SL (r z) := by
    have h := congrArg (fun f => homologyMap f n)
      (integralOpenSupportMap_naturality hLK e.source)
    rw [homologyMap_comp, homologyMap_comp] at h
    exact congrArg (fun f => f z) h
  have hT (z : integralRelativeHomology ((Subtype.val : e.target → Y) ⁻¹' (e '' K)ᶜ) n) :
      integralSupportHomologyRestriction (Set.image_mono hLK) n (TK z) = TL (s z) := by
    have h := congrArg (fun f => homologyMap f n)
      (integralOpenSupportMap_naturality (Set.image_mono (f := e) hLK) e.target)
    rw [homologyMap_comp, homologyMap_comp] at h
    exact congrArg (fun f => f z) h
  have hSinv : SL.symm (integralSupportHomologyRestriction hLK n a) = r (SK.symm a) := by
    apply SL.injective
    rw [LinearEquiv.apply_symm_apply, ← hS, LinearEquiv.apply_symm_apply]
  change TL (integralChartRelativeHomologyEquiv e L hLs n
      (SL.symm (integralSupportHomologyRestriction hLK n a))) =
    integralSupportHomologyRestriction (Set.image_mono hLK) n
      (TK (integralChartRelativeHomologyEquiv e K hKs n (SK.symm a)))
  rw [hSinv, integralChartRelativeHomologyEquiv_naturality e hKs hLs hLK n, hT]

end PoincareConjecture.Proofs.M02.Topology
