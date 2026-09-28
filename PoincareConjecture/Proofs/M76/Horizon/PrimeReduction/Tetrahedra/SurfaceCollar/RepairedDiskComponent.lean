import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SingleBoundaryPiece









set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_old_piece_for_capped_component
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {S B cap Q : Set X} (P : γ → Set X)
    (hP : ∀ c, IsClosed (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : S ∩ B ⊆ ⋃ c, P c) (hPS : ∀ c, P c ⊆ S)
    (c : γ) (hcap : IsClosed cap) (hcontact : cap ∩ S ⊆ P c)
    (hQ : IsConnected Q) (hQsub : Q ⊆ (S ∪ cap) ∩ B) :
    ∃ d, Q ⊆ P d ∪ cap ∧ Q ∩ S ⊆ P d := by
  classical
  let A : γ → Set X := fun d => P d ∪ (if d = c then cap else ∅)
  have hAc (d : γ) : IsClosed (A d) := by
    dsimp only [A]
    split_ifs
    · exact (hP d).union hcap
    · exact (hP d).union isClosed_empty
  have hAPS (d : γ) : A d ∩ S ⊆ P d := by
    rintro x ⟨hx,hxS⟩
    rcases hx with hx | hx
    · exact hx
    · by_cases hdc : d = c
      · subst d
        exact hcontact ⟨by simpa using hx,hxS⟩
      · simpa [hdc] using hx
  have hAdis : Pairwise fun d e => Disjoint (A d) (A e) := by
    intro d e hde
    apply disjoint_left.mpr
    intro x hxd hxe
    by_cases hxS : x ∈ S
    · exact disjoint_left.mp (hdis hde) (hAPS d ⟨hxd,hxS⟩) (hAPS e ⟨hxe,hxS⟩)
    · have hdc : d = c := by
        by_contra hn
        have hxP : x ∈ P d := by simpa [A,hn] using hxd
        exact hxS (hPS d hxP)
      have hec : e = c := by
        by_contra hn
        have hxP : x ∈ P e := by simpa [A,hn] using hxe
        exact hxS (hPS e hxP)
      exact hde (hdc.trans hec.symm)
  have hQcover : Q ⊆ ⋃ d, A d := by
    intro x hx
    rcases hQsub hx with ⟨hxS | hxcap,hxB⟩
    · obtain ⟨d,hd⟩ := mem_iUnion.mp (hcover ⟨hxS,hxB⟩)
      exact mem_iUnion.mpr ⟨d,Or.inl hd⟩
    · exact mem_iUnion.mpr ⟨c,Or.inr (by simpa using hxcap)⟩
  obtain ⟨d,hd,_⟩ := hQ.exists_unique_subset_finite_disjoint_closed A hAc hAdis hQcover
  refine ⟨d,?_,fun x hx => hAPS d ⟨hd hx.1,hx.2⟩⟩
  intro x hx
  rcases hd hx with hxP | hxcap
  · exact Or.inl hxP
  · exact Or.inr (by split_ifs at hxcap <;> simpa using hxcap)

theorem repaired_disk_eq_connectedComponentIn
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {S B R cap ann : Set X} (P : γ → Set X)
    (hP : ∀ c, IsClosed (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : S ∩ B ⊆ ⋃ c, P c) (hPS : ∀ c, P c ⊆ S)
    (c : γ) (hR : R ⊆ S) (hcap : cap ⊆ B)
    (hannB : ann ⊆ B) (hannR : ann ⊆ R) (hannP : ann ⊆ P c)
    (hretain : R ∩ P c ⊆ ann) (hcontact : cap ∩ S ⊆ ann)
    (hclosed : IsClosed (cap ∪ ann)) (hconn : IsConnected (cap ∪ ann)) :
    ∀ x ∈ cap ∪ ann,
      connectedComponentIn ((R ∪ cap) ∩ B) x = cap ∪ ann := by
  classical
  let O := ⋃ d : {d : γ // d ≠ c}, P d
  have hO : IsClosed O := isClosed_iUnion_of_finite fun d => hP d
  have havoid : Disjoint (cap ∪ ann) O := by
    apply disjoint_left.mpr
    intro x hx hxo
    obtain ⟨d,hd⟩ := mem_iUnion.mp hxo
    have hxa : x ∈ ann := by
      rcases hx with hx | hx
      · exact hcontact ⟨hx,hPS d hd⟩
      · exact hx
    exact disjoint_left.mp (hdis d.property) hd (hannP hxa)
  have hsub : cap ∪ ann ⊆ (R ∪ cap) ∩ B := by
    rintro x (hx | hx)
    · exact ⟨Or.inr hx,hcap hx⟩
    · exact ⟨Or.inl (hannR hx),hannB hx⟩
  have hnewcover : (R ∪ cap) ∩ B ⊆ (cap ∪ ann) ∪ O := by
    rintro x ⟨hx | hx,hxB⟩
    · obtain ⟨d,hd⟩ := mem_iUnion.mp (hcover ⟨hR hx,hxB⟩)
      by_cases hdc : d = c
      · exact Or.inl (Or.inr (hretain ⟨hx,hdc ▸ hd⟩))
      · exact Or.inr (mem_iUnion.mpr ⟨⟨d,hdc⟩,hd⟩)
    · exact Or.inl (Or.inl hx)
  intro x hx
  have hxnew := hsub hx
  have hcc := isConnected_connectedComponentIn_iff.mpr hxnew
  have hccsub := connectedComponentIn_subset ((R ∪ cap) ∩ B) x
  have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hcc.isPreconnected
    (cap ∪ ann) O hclosed hO (hccsub.trans hnewcover)
    (by rw [disjoint_iff_inter_eq_empty.mp havoid,inter_empty])
  have hinside : connectedComponentIn ((R ∪ cap) ∩ B) x ⊆ cap ∪ ann := by
    rcases hsplit with h | h
    · exact h
    · exact (disjoint_left.mp havoid hx (h (mem_connectedComponentIn hxnew))).elim
  exact Subset.antisymm hinside (hconn.isPreconnected.subset_connectedComponentIn hx hsub)

end PoincareConjecture.M76
