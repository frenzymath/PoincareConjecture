import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.ClosedInteriorPiece

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem piece_has_interior_point_of_accumulation
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {B S : Set X} (P : γ → Set X) (hP : ∀ c, IsClosed (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : S ∩ B ⊆ ⋃ c, P c) (c : γ) {x : X}
    (hxc : x ∈ P c) (hx : x ∈ closure (S ∩ interior B)) :
    (P c ∩ interior B).Nonempty := by
  classical
  let O := (⋃ d : {d : γ // d ≠ c}, P d)ᶜ
  have hO : IsOpen O :=
    (isClosed_iUnion_of_finite fun d : {d : γ // d ≠ c} => hP d).isOpen_compl
  have hxO : x ∈ O := by
    intro hx
    obtain ⟨d,hd⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hdis d.property) hd hxc
  obtain ⟨y,hyO,hyS,hyB⟩ := _root_.mem_closure_iff.mp hx O hO hxO
  obtain ⟨d,hyd⟩ := mem_iUnion.mp (hcover ⟨hyS,interior_subset hyB⟩)
  have hdc : d = c := by
    by_contra hn
    exact hyO (mem_iUnion.mpr ⟨⟨d,hn⟩,hyd⟩)
  exact ⟨y,hdc ▸ hyd,hyB⟩

theorem closed_piece_eq_side_of_single_boundary
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {B S r : Set X} (hB : IsClosed B) (hS : IsClosed S)
    (P : γ → Set X) (hP : ∀ c, IsClosed (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : S ∩ B ⊆ ⋃ c, P c)
    (c : γ) (hcS : P c ⊆ S) (hcB : P c ⊆ B)
    (hfront : P c ∩ frontier B = r) (hne : (P c \ r).Nonempty)
    (D : Bool → Set X) (hwhole : D false ∪ D true = S)
    (hinter : D false ∩ D true = r)
    (hconn : ∀ b, IsConnected (D b \ r))
    (hclosure : ∀ b, closure (D b \ r) = D b)
    (hout : ¬ S ⊆ B) :
    ∃ b, P c = D b := by
  classical
  let O := (S \ interior B) ∪ ⋃ d : {d : γ // d ≠ c}, P d
  have hO : IsClosed O := (hS.sdiff isOpen_interior).union
    (isClosed_iUnion_of_finite fun d => hP d)
  have hSO : S ⊆ P c ∪ O := by
    intro x hx
    by_cases hxi : x ∈ interior B
    · obtain ⟨d,hxd⟩ := mem_iUnion.mp (hcover ⟨hx,interior_subset hxi⟩)
      by_cases hdc : d = c
      · exact Or.inl (hdc ▸ hxd)
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨d,hdc⟩,hxd⟩))
    · exact Or.inr (Or.inl ⟨hx,hxi⟩)
  have hcontact : P c ∩ O ⊆ r := by
    rintro x ⟨hxc,hxo⟩
    rcases hxo with hxo | hxo
    · exact hfront.subset ⟨hxc,hB.closure_eq.symm ▸ hcB hxc,hxo.2⟩
    · obtain ⟨d,hxd⟩ := mem_iUnion.mp hxo
      exact (disjoint_left.mp (hdis d.property) hxd hxc).elim
  have hDS (b : Bool) : D b ⊆ S := by
    cases b
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hside (b : Bool) (hmeet : ((D b \ r) ∩ P c).Nonempty) : D b ⊆ P c := by
    have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp
      (hconn b).isPreconnected (P c) O (hP c) hO
      (sdiff_subset.trans ((hDS b).trans hSO))
      (show (D b \ r) ∩ (P c ∩ O) = ∅ from eq_empty_iff_forall_notMem.mpr
        (fun x hx => hx.1.2 (hcontact hx.2)))
    have hi : D b \ r ⊆ P c := by
      rcases hsplit with h | h
      · exact h
      · obtain ⟨x,hxd,hxc⟩ := hmeet
        exact (hxd.2 (hcontact ⟨hxc,h hxd⟩)).elim
    rw [←hclosure b]
    exact closure_minimal hi (hP c)
  obtain ⟨x,hxc,hxr⟩ := hne
  have hxS := hwhole.symm.subset (hcS hxc)
  obtain ⟨b,hxb⟩ : ∃ b, x ∈ D b := by
    rcases hxS with hx | hx
    · exact ⟨false,hx⟩
    · exact ⟨true,hx⟩
  have hb := hside b ⟨x,⟨hxb,hxr⟩,hxc⟩
  refine ⟨b,Subset.antisymm ?_ hb⟩
  intro y hyc
  by_contra hyn
  have hyS := hwhole.symm.subset (hcS hyc)
  have hyother : y ∈ D (!b) := by
    cases b
    · exact hyS.resolve_left hyn
    · exact hyS.resolve_right hyn
  have hyr : y ∉ r := by
    intro hy
    have hboth := hinter.symm.subset hy
    cases b
    · exact hyn hboth.1
    · exact hyn hboth.2
  have hbother := hside (!b) ⟨y,⟨hyother,hyr⟩,hyc⟩
  apply hout
  rw [←hwhole]
  cases b
  · exact union_subset (hb.trans hcB) (hbother.trans hcB)
  · exact union_subset (hbother.trans hcB) (hb.trans hcB)

end PoincareConjecture.M76
