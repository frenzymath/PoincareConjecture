import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.SelectedBoundaryExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryPartitionCount

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem boundaryComponentExcess_selected_le_of_eq_section
    {X γ ρ η : Type*} [TopologicalSpace X] [Finite γ] [Finite ρ] [Finite η]
    {S B F : Set X} (hFB : F ⊆ B)
    (P : γ → Set X) (rim : ρ → Set X) (old : ρ → γ)
    (hPclosed : ∀ c, IsClosed (P c)) (hPconn : ∀ c, IsConnected (P c))
    (hPdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hPcover : (⋃ c, P c) = S ∩ B)
    (hrimclosed : ∀ i, IsClosed (rim i)) (hrimconn : ∀ i, IsConnected (rim i))
    (hrimdis : Pairwise fun i j => Disjoint (rim i) (rim j))
    (hrimcover : (⋃ i, rim i) = S ∩ F) (hold : ∀ i, rim i ⊆ P (old i))
    (N : η → Set X) (hNclosed : ∀ k, IsClosed (N k))
    (hNdis : Pairwise fun k l => Disjoint (N k) (N l))
    (hNeq : (⋃ k, N k) ∩ B = S ∩ B) (selected : Set η) :
    boundaryComponentExcess (⋃ k ∈ selected, N k) B F ≤ boundaryComponentExcess S B F := by
  classical
  let := Fintype.ofFinite ρ
  have hNfront : (⋃ k, N k) ∩ F = S ∩ F := by
    ext x
    constructor
    · rintro ⟨hx,hxF⟩
      exact ⟨(hNeq.subset ⟨hx,hFB hxF⟩).1,hxF⟩
    · rintro ⟨hx,hxF⟩
      exact ⟨(hNeq.symm.subset ⟨hx,hFB hxF⟩).1,hxF⟩
  have hrimNF (i) : rim i ⊆ (⋃ k, N k) ∩ F :=
    (subset_iUnion rim i).trans (hrimcover.trans hNfront.symm).subset
  have hside (i : ρ) : ∃ k, rim i ⊆ N k := by
    obtain ⟨k,hk,_⟩ := (hrimconn i).exists_unique_subset_finite_disjoint_closed N hNclosed hNdis
      ((hrimNF i).trans inter_subset_left)
    exact ⟨k,hk⟩
  choose side hside using hside
  choose point hpoint using fun i => (hrimconn i).nonempty
  let C := fun i => connectedComponentIn (N (side i) ∩ B) (point i)
  let label := fun i => (side i,C i)
  let retained := Finset.univ.filter (fun i => side i ∈ selected)
  have hrimB (i : ρ) : rim i ⊆ N (side i) ∩ B :=
    fun x hx => ⟨hside i hx,hFB (hrimNF i hx).2⟩
  have hCold (i : ρ) : C i ⊆ P (old i) := by
    have hconn : IsConnected (C i) := isConnected_connectedComponentIn_iff.mpr (hrimB i (hpoint i))
    have hsub : C i ⊆ ⋃ c, P c := by
      intro x hx
      obtain ⟨hxN,hxB⟩ := connectedComponentIn_subset _ _ hx
      exact hPcover.symm.subset (hNeq.subset ⟨mem_iUnion.mpr ⟨side i,hxN⟩,hxB⟩)
    obtain ⟨c,hc,_⟩ := hconn.exists_unique_subset_finite_disjoint_closed P hPclosed hPdis hsub
    have heq : c = old i := by
      by_contra hn
      exact disjoint_left.mp (hPdis hn) (hc (mem_connectedComponentIn (hrimB i (hpoint i))))
        (hold i (hpoint i))
    simpa only [heq] using hc
  have hrefine : ∀ i ∈ retained, ∀ j ∈ retained, label i = label j → old i = old j := by
    intro i hi j hj heq
    have hCC : C i = C j := congrArg Prod.snd heq
    by_contra hn
    exact disjoint_left.mp (hPdis hn) (hold i (hpoint i))
      (hCold j (hCC ▸ mem_connectedComponentIn (hrimB i (hpoint i))))
  have hle := boundary_partition_excess_le_of_refinement Finset.univ retained
    (Finset.filter_subset _ _) old label hrefine
  have hret : (retained : Set ρ) = {i | side i ∈ selected} := by ext i; simp [retained]
  have himage : ((retained.image label : Finset (η × Set X)) : Set (η × Set X)) =
      label '' {i | side i ∈ selected} := by rw [Finset.coe_image,hret]
  have hrange : ((Finset.univ.image old : Finset γ) : Set γ) = Set.range old := by simp
  rw [←ncard_coe_finset retained,hret,←ncard_coe_finset (retained.image label),himage,
    Finset.card_univ,←ncard_coe_finset (Finset.univ.image old),hrange] at hle
  rw [boundaryComponentExcess_selected_eq_tagged_labels N hNclosed hNdis hFB rim side point
    hrimclosed hrimconn hrimdis (fun i x hx => ⟨hside i hx,(hrimNF i hx).2⟩)
    (hrimcover.trans hNfront.symm) hpoint selected,
    boundaryComponentExcess_eq_of_finite_pieces P rim old hPclosed hPconn hPdis hPcover
      hrimclosed hrimconn hrimdis hrimcover hold]
  simpa only [Nat.card_eq_fintype_card] using hle

end PoincareConjecture.M76
