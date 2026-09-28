import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCapBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v w

namespace Poincare.Topology

attribute [local instance 2000] Submodule.module

variable {X : Type u} [TopologicalSpace X]

theorem integralSmallChains_le_of_refinement {I : Type v} {J : Type w}
    (U : I → Set X) (V : J → Set X) (h : ∀ i, ∃ j, U i ⊆ V j) (n : Nat) :
    integralSmallChains U n ≤ integralSmallChains V n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  apply integralSingularGenerator_mem_small
  obtain ⟨i, hi⟩ := s.property
  obtain ⟨j, hj⟩ := h i
  exact ⟨j, hi.trans hj⟩

theorem integralCap_mem_open_of_small (U K : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) (p + q))
    (phi : (integralRelativeCochains Kᶜ).X q) :
    integralCap p q c ((integralDualMap (integralRelativeProjection Kᶜ)).f q phi) ∈
      LinearMap.range ((integralSubspaceChains U).f p).hom := by
  rw [integralSmallChains_two_eq_sup] at hc
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hc
  rw [← hab, map_add, LinearMap.add_apply,
    integralCap_relative_cochain_zero Kᶜ p q b hb, add_zero]
  exact integralCap_mem_subspace U p q a ha _

def integralSubspaceChainRangeEquiv (U : Set X) (n : Nat) :
    (integralChains U).X n ≃ₗ[Int]
      LinearMap.range ((integralSubspaceChains U).f n).hom := by
  let := integralSubspaceChains_mono U
  exact LinearEquiv.ofInjective ((integralSubspaceChains U).f n).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

def integralLocalizedCap (U K : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) (p + q)) :
    (integralRelativeCochains Kᶜ).X q →ₗ[Int] (integralChains U).X p :=
  (integralSubspaceChainRangeEquiv U p).symm.toLinearMap.comp
    (((integralCap p q c).comp
      ((integralDualMap (integralRelativeProjection Kᶜ)).f q).hom).codRestrict
        (LinearMap.range ((integralSubspaceChains U).f p).hom)
          (integralCap_mem_open_of_small U K p q c hc))

theorem integralLocalizedCap_inclusion (U K : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) (p + q))
    (phi : (integralRelativeCochains Kᶜ).X q) :
    (integralSubspaceChains U).f p (integralLocalizedCap U K p q c hc phi) =
      integralCap p q c ((integralDualMap (integralRelativeProjection Kᶜ)).f q phi) := by
  exact congrArg Subtype.val ((integralSubspaceChainRangeEquiv U p).apply_symm_apply
    ⟨_, integralCap_mem_open_of_small U K p q c hc phi⟩)

abbrev integralCommonCapCover (U K V L : Set X) : Bool × Bool → Set X :=
  fun i => integralBinaryCover U Kᶜ i.1 ∩ integralBinaryCover V Lᶜ i.2

theorem integralCommonCapCover_small_left (U K V L : Set X) (n : Nat) :
    integralSmallChains (integralCommonCapCover U K V L) n ≤
      integralSmallChains (integralBinaryCover U Kᶜ) n :=
  integralSmallChains_le_of_refinement (integralCommonCapCover U K V L)
    (integralBinaryCover U Kᶜ) (fun i => ⟨i.1, Set.inter_subset_left⟩) n

theorem integralCommonCapCover_small_right (U K V L : Set X) (n : Nat) :
    integralSmallChains (integralCommonCapCover U K V L) n ≤
      integralSmallChains (integralBinaryCover V Lᶜ) n :=
  integralSmallChains_le_of_refinement (integralCommonCapCover U K V L)
    (integralBinaryCover V Lᶜ) (fun i => ⟨i.2, Set.inter_subset_right⟩) n

theorem integralCommonCapCover_small_inter (U K V L : Set X) (n : Nat) :
    integralSmallChains (integralCommonCapCover U K V L) n ≤
      integralSmallChains (integralBinaryCover (U ∩ V) (K ∩ L)ᶜ) n := by
  apply integralSmallChains_le_of_refinement
  rintro ⟨i, j⟩
  cases i <;> cases j
  · exact ⟨false, fun _ hx h => hx.1 h.1⟩
  · exact ⟨false, fun _ hx h => hx.1 h.1⟩
  · exact ⟨false, fun _ hx h => hx.2 h.2⟩
  · exact ⟨true, fun _ hx => hx⟩

theorem integralCommonCapCover_open (U K V L : Set X)
    (hU : IsOpen U) (hK : IsClosed K) (hV : IsOpen V) (hL : IsClosed L)
    (i : Bool × Bool) : IsOpen (integralCommonCapCover U K V L i) := by
  rcases i with ⟨i, j⟩
  cases i <;> cases j
  · exact hK.isOpen_compl.inter hL.isOpen_compl
  · exact hK.isOpen_compl.inter hV
  · exact hU.inter hL.isOpen_compl
  · exact hU.inter hV

omit [TopologicalSpace X] in
theorem integralCommonCapCover_covers (U K V L : Set X)
    (hK : K ⊆ U) (hL : L ⊆ V) :
    (⋃ i, integralCommonCapCover U K V L i) = Set.univ := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hxK : x ∈ K
  · by_cases hxL : x ∈ L
    · exact ⟨(true, true), hK hxK, hL hxL⟩
    · exact ⟨(true, false), hK hxK, hxL⟩
  · by_cases hxL : x ∈ L
    · exact ⟨(false, true), hxK, hL hxL⟩
    · exact ⟨(false, false), hxK, hxL⟩

end Poincare.Topology
