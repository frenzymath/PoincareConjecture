import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryComponentExcess
import Mathlib.Data.Set.Card

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem connectedComponentIn_selected_union_eq_member
    {X η : Type*} [TopologicalSpace X] [Finite η]
    (S : η → Set X) (hclosed : ∀ k, IsClosed (S k))
    (hdis : Pairwise fun k l => Disjoint (S k) (S l))
    (selected : Set η) {B : Set X} {k : η} (hk : k ∈ selected)
    {x : X} (hx : x ∈ S k ∩ B) :
    connectedComponentIn ((⋃ k ∈ selected, S k) ∩ B) x =
      connectedComponentIn (S k ∩ B) x := by
  let U := (⋃ k ∈ selected, S k) ∩ B
  have hmember : S k ∩ B ⊆ U := fun y hy =>
    ⟨mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hk,hy.1⟩⟩,hy.2⟩
  have hxU := hmember hx
  have hconn := isConnected_connectedComponentIn_iff.mpr hxU
  have hsub : connectedComponentIn U x ⊆ ⋃ k, S k := by
    intro y hy
    obtain ⟨k,hk⟩ := mem_iUnion.mp (connectedComponentIn_subset U x hy).1
    obtain ⟨_,hy⟩ := mem_iUnion.mp hk
    exact mem_iUnion.mpr ⟨k,hy⟩
  obtain ⟨l,hl,_⟩ := hconn.exists_unique_subset_finite_disjoint_closed S hclosed hdis hsub
  have hlk : l = k := by
    by_contra hne
    exact disjoint_left.mp (hdis hne) (hl (mem_connectedComponentIn hxU)) hx.1
  subst l
  apply Subset.antisymm
  · exact hconn.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hxU)
      (fun y hy => ⟨hl hy,(connectedComponentIn_subset U x hy).2⟩)
  · exact connectedComponentIn_mono x hmember

theorem selected_boundary_component_counts_eq_tagged_labels
    {X ρ η : Type*} [TopologicalSpace X] [Finite ρ] [Finite η]
    (S : η → Set X) (hSclosed : ∀ k, IsClosed (S k))
    (hSdis : Pairwise fun k l => Disjoint (S k) (S l))
    {B F : Set X} (hFB : F ⊆ B)
    (rim : ρ → Set X) (side : ρ → η) (point : ρ → X)
    (hrimclosed : ∀ i, IsClosed (rim i)) (hrimconn : ∀ i, IsConnected (rim i))
    (hrimdis : Pairwise fun i j => Disjoint (rim i) (rim j))
    (hrimside : ∀ i, rim i ⊆ S (side i) ∩ F)
    (hrimcover : (⋃ i, rim i) = (⋃ k, S k) ∩ F)
    (hpoint : ∀ i, point i ∈ rim i) (selected : Set η) :
    (connectedComponentIn ((⋃ k ∈ selected, S k) ∩ F) ''
      ((⋃ k ∈ selected, S k) ∩ F)).ncard = {i | side i ∈ selected}.ncard ∧
      (connectedComponentIn ((⋃ k ∈ selected, S k) ∩ B) ''
        ((⋃ k ∈ selected, S k) ∩ F)).ncard =
        ((fun i => (side i,connectedComponentIn (S (side i) ∩ B) (point i))) ''
          {i | side i ∈ selected}).ncard := by
  classical
  let U := ⋃ k ∈ selected, S k
  let retained : Set ρ := {i | side i ∈ selected}
  let C := fun i => connectedComponentIn (S (side i) ∩ B) (point i)
  let label := fun i => (side i,C i)
  have hrimB (i : ρ) : rim i ⊆ S (side i) ∩ B := fun x hx =>
    ⟨(hrimside i hx).1,hFB (hrimside i hx).2⟩
  have hptB (i : ρ) : point i ∈ S (side i) ∩ B := hrimB i (hpoint i)
  have hkeep {i : ρ} {x : X} (hx : x ∈ rim i) (hxU : x ∈ U) : i ∈ retained := by
    obtain ⟨k,hk⟩ := mem_iUnion.mp hxU
    obtain ⟨hk,hy⟩ := mem_iUnion.mp hk
    have heq : side i = k := by
      by_contra hn
      exact disjoint_left.mp (hSdis hn) (hrimside i hx).1 hy
    change side i ∈ selected
    rwa [heq]
  have hkeepsub (i : ρ) (hi : i ∈ retained) : rim i ⊆ U ∩ F := by
    intro x hx
    exact ⟨mem_iUnion.mpr ⟨side i,mem_iUnion.mpr ⟨hi,(hrimside i hx).1⟩⟩,
      (hrimside i hx).2⟩
  have hretcover : (⋃ i : retained, rim i) = U ∩ F := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hkeepsub i i.property hi
    · intro x hx
      have hxall : x ∈ ⋃ k, S k := by
        obtain ⟨k,hk⟩ := mem_iUnion.mp hx.1
        obtain ⟨_,hk⟩ := mem_iUnion.mp hk
        exact mem_iUnion.mpr ⟨k,hk⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hrimcover.symm.subset ⟨hxall,hx.2⟩)
      exact mem_iUnion.mpr ⟨⟨i,hkeep hi hx.1⟩,hi⟩
  have hretcomp (i : retained) {x : X} (hx : x ∈ rim i) :
      connectedComponentIn (U ∩ F) x = rim i :=
    finite_closed_connected_piece_eq_component (fun i : retained => rim i)
      (fun i => hrimclosed i) (fun i => hrimconn i)
      (fun i j h => hrimdis (fun heq => h (Subtype.ext heq))) hretcover i hx
  have hboundary : connectedComponentIn (U ∩ F) '' (U ∩ F) = rim '' retained := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hretcover.symm.subset hx)
      exact ⟨i,i.property,(hretcomp i hi).symm⟩
    · rintro _ ⟨i,hi,rfl⟩
      exact ⟨point i,hkeepsub i hi (hpoint i),hretcomp ⟨i,hi⟩ (hpoint i)⟩
  have hriminj : Function.Injective rim := by
    intro i j heq
    by_contra hn
    exact disjoint_left.mp (hrimdis hn) (hpoint i) (heq ▸ hpoint i)
  have hcomponent (i : ρ) (hi : i ∈ retained) {x : X} (hx : x ∈ rim i) :
      connectedComponentIn (U ∩ B) x = C i := by
    rw [connectedComponentIn_selected_union_eq_member S hSclosed hSdis selected hi (hrimB i hx)]
    exact (connectedComponentIn_eq ((hrimconn i).isPreconnected.subset_connectedComponentIn
      (hpoint i) (hrimB i) hx)).symm
  have hoccupied : connectedComponentIn (U ∩ B) '' (U ∩ F) = C '' retained := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hretcover.symm.subset hx)
      exact ⟨i,i.property,(hcomponent i i.property hi).symm⟩
    · rintro _ ⟨i,hi,rfl⟩
      exact ⟨point i,hkeepsub i hi (hpoint i),hcomponent i hi (hpoint i)⟩
  have hforget : InjOn (Prod.snd : η × Set X → Set X) (label '' retained) := by
    rintro _ ⟨i,hi,rfl⟩ _ ⟨j,hj,rfl⟩ heq
    have hc : C i = C j := heq
    have hs : side i = side j := by
      by_contra hn
      have hxj : point i ∈ C j := hc ▸ mem_connectedComponentIn (hptB i)
      exact disjoint_left.mp (hSdis hn) (hptB i).1
        (connectedComponentIn_subset _ _ hxj).1
    exact Prod.ext hs hc
  have htagcount : (C '' retained).ncard = (label '' retained).ncard := by
    have h := hforget.ncard_image
    rw [←image_comp] at h
    exact h
  change (connectedComponentIn (U ∩ F) '' (U ∩ F)).ncard = retained.ncard ∧
    (connectedComponentIn (U ∩ B) '' (U ∩ F)).ncard = (label '' retained).ncard
  constructor
  · rw [hboundary,ncard_image_of_injective _ hriminj]
  · rw [hoccupied,htagcount]

theorem boundaryComponentExcess_selected_eq_tagged_labels
    {X ρ η : Type*} [TopologicalSpace X] [Finite ρ] [Finite η]
    (S : η → Set X) (hSclosed : ∀ k, IsClosed (S k))
    (hSdis : Pairwise fun k l => Disjoint (S k) (S l))
    {B F : Set X} (hFB : F ⊆ B)
    (rim : ρ → Set X) (side : ρ → η) (point : ρ → X)
    (hrimclosed : ∀ i, IsClosed (rim i)) (hrimconn : ∀ i, IsConnected (rim i))
    (hrimdis : Pairwise fun i j => Disjoint (rim i) (rim j))
    (hrimside : ∀ i, rim i ⊆ S (side i) ∩ F)
    (hrimcover : (⋃ i, rim i) = (⋃ k, S k) ∩ F)
    (hpoint : ∀ i, point i ∈ rim i) (selected : Set η) :
    boundaryComponentExcess (⋃ k ∈ selected, S k) B F =
      {i | side i ∈ selected}.ncard -
        ((fun i => (side i,connectedComponentIn (S (side i) ∩ B) (point i))) ''
          {i | side i ∈ selected}).ncard := by
  obtain ⟨hboundary,hoccupied⟩ := selected_boundary_component_counts_eq_tagged_labels
    S hSclosed hSdis hFB rim side point hrimclosed hrimconn hrimdis hrimside hrimcover hpoint selected
  exact congrArg₂ (fun a b : ℕ => a - b) hboundary hoccupied

end PoincareConjecture.M76
