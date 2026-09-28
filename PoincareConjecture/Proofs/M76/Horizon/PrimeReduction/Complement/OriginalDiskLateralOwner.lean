import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripBall
import Mathlib.Analysis.Normed.Module.Connected









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_unique_lateral_owner_and_pole
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (B : Bool → Set X)
    (hclosed : ∀ b, IsClosed (B b)) (hdis : Disjoint (B false) (B true))
    (hfront : P.map '' (Q ×ˢ Icc (-1 : ℝ) 1) ⊆ B false ∪ B true) :
    ∃ b : Bool,
      P.map '' (Q ×ˢ Icc (-1 : ℝ) 1) ⊆ B b ∧
      (∀ d, P.map '' (Q ×ˢ J) ⊆ B d ↔ d = b) ∧
      ∃ x : Q, P.map ((x : V2),(3 / 4 : ℝ)) ∈ B b ∧
        P.map ((x : V2),(3 / 4 : ℝ)) ∉ P.map '' (Q ×ˢ J) := by
  have hfull : Q ×ˢ Icc (-1 : ℝ) 1 ⊆ D ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono sphere_subset_closedBall subset_rfl
  have hconn : IsConnected (P.map '' (Q ×ˢ Icc (-1 : ℝ) 1)) :=
    ((isConnected_sphere (by simp) (0 : V2) zero_le_one).prod
      (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))).image _
        (P.polyhedral.continuousOn.mono hfull)
  have howner : ∃ b, P.map '' (Q ×ˢ Icc (-1 : ℝ) 1) ⊆ B b := by
    by_cases h0 : P.map '' (Q ×ˢ Icc (-1 : ℝ) 1) ⊆ B false
    · exact ⟨false,h0⟩
    · refine ⟨true,?_⟩
      by_contra h1
      obtain ⟨x,hx,hx0⟩ := Set.not_subset.mp h0
      obtain ⟨y,hy,hy1⟩ := Set.not_subset.mp h1
      have hx1 := (hfront hx).resolve_left hx0
      have hy0 := (hfront hy).resolve_right hy1
      obtain ⟨z,_,hz0,hz1⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected
        (B false) (B true) (hclosed false) (hclosed true) hfront
        ⟨y,hy,hy0⟩ ⟨x,hx,hx1⟩
      exact disjoint_left.mp hdis hz0 hz1
  obtain ⟨b,hb⟩ := howner
  obtain ⟨x,hx⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
  have hxD : x ∈ D := sphere_subset_closedBall hx
  have hsmall : Q ×ˢ J ⊆ Q ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hz,ht⟩
    exact ⟨hz,by linarith [ht.1],by linarith [ht.2]⟩
  have hx0 : P.map (x,0) ∈ P.map '' (Q ×ˢ J) :=
    ⟨(x,0),⟨hx,by norm_num⟩,rfl⟩
  refine ⟨b,hb,?_,⟨x,hx⟩,hb ⟨(x,3/4),⟨hx,by norm_num⟩,rfl⟩,?_⟩
  · intro d
    constructor
    · intro hd
      by_contra hne
      have hB := hb ((image_mono hsmall) hx0)
      have hD := hd hx0
      cases b <;> cases d
      · exact hne rfl
      · exact disjoint_left.mp hdis hB hD
      · exact disjoint_left.mp hdis hD hB
      · exact hne rfl
    · rintro rfl
      exact (image_mono hsmall).trans hb
  · rintro ⟨z,hz,heq⟩
    have hzi := hfull (hsmall hz)
    have hxi : (x,(3 / 4 : ℝ)) ∈ D ×ˢ Icc (-1 : ℝ) 1 := ⟨hxD,by norm_num⟩
    have ht := congrArg Prod.snd (P.injective hzi hxi heq)
    dsimp at ht
    linarith [hz.2.2]

theorem exists_unique_exterior_lateral_owner_and_pole
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R H K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (B : Bool → Set X)
    (hclosed : ∀ b, IsClosed (B b)) (hdis : Disjoint (B false) (B true))
    (hR : R = H ∩ (interior K)ᶜ) (hK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) (interior H)) :
    ∃ b : Bool,
      P.map '' (Q ×ˢ Icc (-1 : ℝ) 1) ⊆ B b ∧
      (∀ d, P.map '' (Q ×ˢ J) ⊆ B d ↔ d = b) ∧
      ∃ x : Q, P.map ((x : V2),(3 / 4 : ℝ)) ∈ B b ∧
        P.map ((x : V2),(3 / 4 : ℝ)) ∉ P.map '' (Q ×ˢ J) := by
  apply P.exists_unique_lateral_owner_and_pole B hclosed hdis
  rintro _ ⟨z,hz,rfl⟩
  have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 := ⟨sphere_subset_closedBall hz.1,hz.2⟩
  have hfront := (P.proper z hzfull).mpr hz.1
  have hfront' := (congrArg frontier hR).subset hfront
  rcases frontier_inter_subset H (interior K)ᶜ hfront' with hH | hK'
  · exact False.elim (hH.1.2 (hsmall hzfull))
  · apply hK.subset
    apply frontier_interior_subset
    simpa only [frontier_compl] using hK'.2

end PoincareConjecture.M76.OriginalDiskProduct
