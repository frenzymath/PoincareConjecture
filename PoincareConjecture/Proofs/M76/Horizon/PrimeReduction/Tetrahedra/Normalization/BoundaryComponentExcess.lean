import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SingleBoundaryPiece









set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

noncomputable def boundaryComponentExcess {X : Type*} [TopologicalSpace X]
    (S B F : Set X) : ℕ :=
  (connectedComponentIn (S ∩ F) '' (S ∩ F)).ncard -
    (connectedComponentIn (S ∩ B) '' (S ∩ F)).ncard

theorem finite_closed_connected_piece_eq_component
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {A : Set X} (P : γ → Set X)
    (hclosed : ∀ c, IsClosed (P c)) (hconn : ∀ c, IsConnected (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d)) (hcover : (⋃ c, P c) = A)
    (c : γ) {x : X} (hx : x ∈ P c) : connectedComponentIn A x = P c := by
  have hsub (d : γ) : P d ⊆ A := (subset_iUnion P d).trans hcover.subset
  have hxA := hsub c hx
  obtain ⟨d,hd,_⟩ := (isConnected_connectedComponentIn_iff.mpr hxA).exists_unique_subset_finite_disjoint_closed
    P hclosed hdis
      ((connectedComponentIn_subset A x).trans hcover.symm.subset)
  have hdc : d = c := by
    by_contra hn
    exact disjoint_left.mp (hdis hn) (hd (mem_connectedComponentIn hxA)) hx
  subst d
  exact Subset.antisymm hd ((hconn c).isPreconnected.subset_connectedComponentIn hx (hsub c))

theorem boundaryComponentExcess_eq_of_finite_pieces
    {X γ ρ : Type*} [TopologicalSpace X] [Finite γ] [Finite ρ]
    {S B F : Set X} (P : γ → Set X) (rim : ρ → Set X) (owner : ρ → γ)
    (hPclosed : ∀ c, IsClosed (P c)) (hPconn : ∀ c, IsConnected (P c))
    (hPdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hPcover : (⋃ c, P c) = S ∩ B)
    (hrimclosed : ∀ j, IsClosed (rim j)) (hrimconn : ∀ j, IsConnected (rim j))
    (hrimdis : Pairwise fun j k => Disjoint (rim j) (rim k))
    (hrimcover : (⋃ j, rim j) = S ∩ F) (howner : ∀ j, rim j ⊆ P (owner j)) :
    boundaryComponentExcess S B F = Nat.card ρ - (Set.range owner).ncard := by
  classical
  have hPcomp := finite_closed_connected_piece_eq_component P hPclosed hPconn hPdis hPcover
  have hrimcomp := finite_closed_connected_piece_eq_component rim hrimclosed hrimconn hrimdis hrimcover
  have hPinj : Function.Injective P := by
    intro c d heq
    by_contra hn
    obtain ⟨x,hx⟩ := (hPconn c).nonempty
    exact disjoint_left.mp (hPdis hn) hx (heq ▸ hx)
  have hriminj : Function.Injective rim := by
    intro j k heq
    by_contra hn
    obtain ⟨x,hx⟩ := (hrimconn j).nonempty
    exact disjoint_left.mp (hrimdis hn) hx (heq ▸ hx)
  have hboundary : connectedComponentIn (S ∩ F) '' (S ∩ F) = Set.range rim := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hrimcover.symm.subset hx)
      exact ⟨j,(hrimcomp j hj).symm⟩
    · rintro _ ⟨j,rfl⟩
      obtain ⟨x,hx⟩ := (hrimconn j).nonempty
      exact ⟨x,hrimcover.subset (mem_iUnion.mpr ⟨j,hx⟩),hrimcomp j hx⟩
  have hpieces : connectedComponentIn (S ∩ B) '' (S ∩ F) = P '' Set.range owner := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hrimcover.symm.subset hx)
      exact ⟨owner j,mem_range_self j,(hPcomp (owner j) (howner j hj)).symm⟩
    · rintro _ ⟨c,⟨j,rfl⟩,rfl⟩
      obtain ⟨x,hx⟩ := (hrimconn j).nonempty
      exact ⟨x,hrimcover.subset (mem_iUnion.mpr ⟨j,hx⟩),hPcomp (owner j) (howner j hx)⟩
  simp only [boundaryComponentExcess,hboundary,hpieces,ncard_range_of_injective hriminj,
    ncard_image_of_injective _ hPinj]

theorem boundaryComponentExcess_eq_zero_of_preconnected_frontiers
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {S B F : Set X} (P : γ → Set X)
    (hPclosed : ∀ c, IsClosed (P c)) (hPconn : ∀ c, IsConnected (P c))
    (hPdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hPcover : (⋃ c, P c) = S ∩ B) (hF : IsClosed F) (hFB : F ⊆ B)
    (hfront : ∀ c, IsPreconnected (P c ∩ F)) : boundaryComponentExcess S B F = 0 := by
  classical
  let δ := {c : γ // (P c ∩ F).Nonempty}
  let rim : δ → Set X := fun c => P c.val ∩ F
  have hrimdis : Pairwise fun c d : δ => Disjoint (rim c) (rim d) := by
    intro c d hcd
    exact (hPdis (fun h => hcd (Subtype.ext h))).mono inter_subset_left inter_subset_left
  have hrimcover : (⋃ c, rim c) = S ∩ F := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      exact ⟨(hPcover.subset (mem_iUnion.mpr ⟨c.val,hc.1⟩)).1,hc.2⟩
    · rintro x ⟨hxS,hxF⟩
      obtain ⟨c,hc⟩ := mem_iUnion.mp (hPcover.symm.subset ⟨hxS,hFB hxF⟩)
      exact mem_iUnion.mpr ⟨⟨c,x,hc,hxF⟩,hc,hxF⟩
  have heq := boundaryComponentExcess_eq_of_finite_pieces P rim Subtype.val
    hPclosed hPconn hPdis hPcover (fun c => (hPclosed c.val).inter hF)
    (fun c => ⟨c.property,hfront c.val⟩) hrimdis hrimcover (fun _ => inter_subset_left)
  rw [heq,ncard_range_of_injective Subtype.val_injective,Nat.sub_self]

end PoincareConjecture.M76
