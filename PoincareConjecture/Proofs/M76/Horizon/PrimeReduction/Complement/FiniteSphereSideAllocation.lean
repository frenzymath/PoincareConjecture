import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X]

theorem IsPreconnected.subset_rim_complement_or_complement
    {s A r : Set X} (hs : IsPreconnected s) (hA : IsClosed A)
    (hopen : IsOpen (A \ r)) (hmiss : Disjoint s r) :
    s ⊆ A \ r ∨ s ⊆ Aᶜ := by
  classical
  by_cases hdis : Disjoint s A
  · exact Or.inr fun x hx hxa => disjoint_left.mp hdis hx hxa
  · left
    obtain ⟨y,hys,hya⟩ := not_disjoint_iff.mp hdis
    intro x hx
    by_contra hxo
    have hcover : s ⊆ A ∪ (A \ r)ᶜ := by
      intro z _
      by_cases hz : z ∈ A
      · exact Or.inl hz
      · exact Or.inr fun ho => hz ho.1
    obtain ⟨z,hzs,hzA,hzO⟩ := isPreconnected_closed_iff.mp hs A (A \ r)ᶜ
      hA hopen.isClosed_compl hcover ⟨y,hys,hya⟩ ⟨x,hx,hxo⟩
    exact hzO ⟨hzA,fun hzr => disjoint_left.mp hmiss hzs hzr⟩

namespace Set

theorem closure_subset_complement_of_open_disjoint
    {U O : Set X} (hO : IsOpen O) (hmiss : Disjoint O U) : closure U ⊆ Oᶜ :=
  closure_minimal (fun _ hx ho => disjoint_left.mp hmiss ho hx) hO.isClosed_compl

theorem pairwise_disjoint_excluded_sides {ι : Type*}
    (A r : ι → Set X) {U : Set X}
    (hAclosed : ∀ i, IsClosed (A i)) (hAconn : ∀ i, IsPreconnected (A i))
    (hopen : ∀ i, IsOpen (A i \ r i))
    (hrA : ∀ i, r i ⊆ A i) (hrne : ∀ i, (r i).Nonempty)
    (hrattach : ∀ i, r i ⊆ closure U)
    (hexcluded : ∀ i, Disjoint (A i \ r i) U)
    (hrdis : Pairwise fun i j => Disjoint (r i) (r j)) :
    Pairwise fun i j => Disjoint (A i) (A j) := by
  have hclosure (i : ι) : closure U ⊆ (A i \ r i)ᶜ :=
    closure_subset_complement_of_open_disjoint (hopen i) (hexcluded i)
  have hmiss (i j : ι) (hij : i ≠ j) : Disjoint (A i) (r j) := by
    apply disjoint_left.mpr
    intro x hx hrj
    have hnri : x ∉ r i := fun hri => disjoint_left.mp (hrdis hij) hri hrj
    exact hclosure i (hrattach j hrj) ⟨hx,hnri⟩
  intro i j hij
  rcases (hAconn i).subset_rim_complement_or_complement
      (hAclosed j) (hopen j) (hmiss i j hij) with hinside | houtside
  · obtain ⟨x,hxr⟩ := hrne i
    exact False.elim (hclosure j (hrattach i hxr) (hinside (hrA i hxr)))
  · exact disjoint_left.mpr fun x hx hj => houtside hx hj

theorem exists_pairwise_disjoint_excluded_side_family {ι : Type*}
    (A : ι → Bool → Set X) (r : ι → Set X) {U : Set X}
    (hU : IsConnected U)
    (hclosed : ∀ i b, IsClosed (A i b))
    (hconn : ∀ i b, IsPreconnected (A i b))
    (hopen : ∀ i b, IsOpen (A i b \ r i))
    (hcover : ∀ i, A i false ∪ A i true = univ)
    (hinter : ∀ i, A i false ∩ A i true = r i)
    (hrne : ∀ i, (r i).Nonempty)
    (hUmiss : ∀ i, Disjoint U (r i))
    (hrattach : ∀ i, r i ⊆ closure U)
    (hrdis : Pairwise fun i j => Disjoint (r i) (r j)) :
    ∃ excluded : ι → Bool,
      (∀ i, U ⊆ A i (!(excluded i)) \ r i) ∧
      (∀ i, Disjoint (A i (excluded i)) U) ∧
      (∀ i b, U ⊆ A i b \ r i ↔ b = !(excluded i)) ∧
      Pairwise (fun i j => Disjoint (A i (excluded i)) (A j (excluded j))) := by
  classical
  have hrA (i : ι) (b : Bool) : r i ⊆ A i b := by
    cases b
    · exact fun _ hx => ((hinter i).symm.subset hx).1
    · exact fun _ hx => ((hinter i).symm.subset hx).2
  have hchoose (i : ι) : ∃ b : Bool,
      U ⊆ A i (!b) \ r i ∧ Disjoint (A i b) U := by
    rcases hU.isPreconnected.subset_rim_complement_or_complement
      (hclosed i false) (hopen i false) (hUmiss i) with hfalse | hnfalse
    · refine ⟨true,hfalse,disjoint_left.mpr ?_⟩
      intro x hxt hxU
      exact (hfalse hxU).2 ((hinter i).subset ⟨(hfalse hxU).1,hxt⟩)
    · refine ⟨false,?_,disjoint_left.mpr fun x hxf hxU => hnfalse hxU hxf⟩
      intro x hx
      refine ⟨?_,fun hr => disjoint_left.mp (hUmiss i) hx hr⟩
      exact ((hcover i).symm.subset (mem_univ x)).resolve_left (hnfalse hx)
  choose excluded hinside hmiss using hchoose
  refine ⟨excluded,hinside,hmiss,?_,?_⟩
  · intro i b
    constructor
    · intro hb
      by_contra hne
      have heq : b = excluded i := by
        cases hb' : b <;> cases hi : excluded i <;> simp_all only [Bool.not_false,
          Bool.not_true, Bool.false_eq_true, not_false_eq_true, not_true_eq_false]
      obtain ⟨x,hx⟩ := hU.nonempty
      exact disjoint_left.mp (hmiss i) (heq ▸ (hb hx).1) hx
    · intro heq
      simpa only [heq] using hinside i
  · exact pairwise_disjoint_excluded_sides (fun i => A i (excluded i)) r
      (fun i => hclosed i _) (fun i => hconn i _) (fun i => hopen i _)
      (fun i => hrA i _) hrne hrattach
      (fun i => (hmiss i).mono_left sdiff_subset) hrdis

end Set
