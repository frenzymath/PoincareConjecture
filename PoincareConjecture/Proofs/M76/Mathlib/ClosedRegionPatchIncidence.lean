import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence












set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]





theorem IsConnected.exists_closure_subset_of_finite_closed_cover
    {ι : Type*} [Finite ι] {s g : Set X} (hs : IsConnected s)
    (D : ι → Set X) (hD : ∀ i, IsClosed (D i))
    (hcover : s ⊆ ⋃ i, D i)
    (hpair : Pairwise (fun i j => D i ∩ D j ⊆ g))
    (havoid : Disjoint s g) : ∃ i, closure s ⊆ D i := by
  classical
  obtain ⟨x, hxs⟩ := hs.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hxs)
  let O : Set X := ⋃ j : {j : ι // j ≠ i}, D j
  have hO : IsClosed O := isClosed_iUnion_of_finite (fun j => hD j)
  have hsplit : s ⊆ D i ∪ O := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hinter : s ∩ (D i ∩ O) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hys, hyi, hyO⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyO
    exact disjoint_left.mp havoid hys (hpair (Ne.symm j.property) ⟨hyi, hyj⟩)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hs.isPreconnected
    (D i) O (hD i) hO hsplit hinter
  have hsub : s ⊆ D i := hside.resolve_right fun hsO => by
    have hx : x ∈ s ∩ (D i ∩ O) := ⟨hxs, hxi, hsO hxs⟩
    rw [hinter] at hx
    exact hx
  exact ⟨i, closure_minimal hsub (hD i)⟩





theorem IsConnected.closure_subset_four_region_of_arc_witnesses
    {s : Set X} (hs : IsConnected s) (arc D : Bool × Bool → Set X)
    {a b : X} (hArc : Pairwise (fun i j => arc i ∩ arc j = {a, b}))
    (hD : ∀ i, IsClosed (D i))
    (hcover : s ⊆ ⋃ i, D i)
    (hpair : Pairwise (fun i j => D i ∩ D j ⊆ ⋃ k, arc k))
    (hcontact : ∀ i, D i ∩ (⋃ j, arc j) = arc (false, i.2) ∪ arc (true, i.1))
    (havoid : Disjoint s (⋃ j, arc j)) (k : Bool × Bool)
    (hw₀ : ∃ x ∈ closure s, x ∈ arc (false, k.2) ∧ x ∉ ({a, b} : Set X))
    (hw₁ : ∃ x ∈ closure s, x ∈ arc (true, k.1) ∧ x ∉ ({a, b} : Set X)) :
    closure s ⊆ D k := by
  obtain ⟨i, hi⟩ := hs.exists_closure_subset_of_finite_closed_cover D hD hcover hpair havoid
  have hi₂ : i.2 = k.2 := by
    obtain ⟨x, hxs, hxa, hxm⟩ := hw₀
    have hxrim := (hcontact i).subset ⟨hi hxs, mem_iUnion.mpr ⟨(false, k.2), hxa⟩⟩
    rcases hxrim with hxf | hxt
    · by_contra hne
      have hidx : (false, k.2) ≠ (false, i.2) :=
        fun h => hne (congrArg Prod.snd h).symm
      exact hxm ((hArc hidx).subset ⟨hxa, hxf⟩)
    · have hidx : (false, k.2) ≠ (true, i.1) := by simp
      exact (hxm ((hArc hidx).subset ⟨hxa, hxt⟩)).elim
  have hi₁ : i.1 = k.1 := by
    obtain ⟨x, hxs, hxa, hxm⟩ := hw₁
    have hxrim := (hcontact i).subset ⟨hi hxs, mem_iUnion.mpr ⟨(true, k.1), hxa⟩⟩
    rcases hxrim with hxf | hxt
    · have hidx : (true, k.1) ≠ (false, i.2) := by simp
      exact (hxm ((hArc hidx).subset ⟨hxa, hxf⟩)).elim
    · by_contra hne
      have hidx : (true, k.1) ≠ (true, i.1) :=
        fun h => hne (congrArg Prod.snd h).symm
      exact hxm ((hArc hidx).subset ⟨hxa, hxt⟩)
  have hik : i = k := Prod.ext hi₁ hi₂
  exact hik ▸ hi

end Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]





theorem IsFinitePLBallPair.subset_four_region_of_arc_witnesses
    {d q : Set X} (hd : IsFinitePLBallPair E d q)
    (arc D : Bool × Bool → Set X) {a b : X}
    (hArc : Pairwise (fun i j => arc i ∩ arc j = {a, b}))
    (hD : ∀ i, IsClosed (D i)) (hcover : d ⊆ ⋃ i, D i)
    (hpair : Pairwise (fun i j => D i ∩ D j ⊆ ⋃ k, arc k))
    (hcontact : ∀ i, D i ∩ (⋃ j, arc j) = arc (false, i.2) ∪ arc (true, i.1))
    (hdgraph : d ∩ (⋃ j, arc j) ⊆ q) (k : Bool × Bool)
    (hw₀ : ∃ x ∈ d, x ∈ arc (false, k.2) ∧ x ∉ ({a, b} : Set X))
    (hw₁ : ∃ x ∈ d, x ∈ arc (true, k.1) ∧ x ∉ ({a, b} : Set X)) : d ⊆ D k := by
  have havoid : Disjoint (d \ q) (⋃ j, arc j) := by
    apply disjoint_left.mpr
    intro x hx hxg
    exact hx.2 (hdgraph ⟨hx.1, hxg⟩)
  have hw₀' : ∃ x ∈ closure (d \ q), x ∈ arc (false, k.2) ∧ x ∉ ({a, b} : Set X) := by
    rwa [hd.closure_sdiff]
  have hw₁' : ∃ x ∈ closure (d \ q), x ∈ arc (true, k.1) ∧ x ∉ ({a, b} : Set X) := by
    rwa [hd.closure_sdiff]
  have hsub := hd.isConnected_sdiff.closure_subset_four_region_of_arc_witnesses
    arc D hArc hD (sdiff_subset.trans hcover) hpair hcontact havoid k hw₀' hw₁'
  rwa [hd.closure_sdiff] at hsub






theorem IsFinitePLBallPair.attached_to_four_region_of_graph_contact
    {d u w : Set X} (hd : IsFinitePLBallPair E d (u ∪ w))
    (arc D : Bool × Bool → Set X) {a b c e : X}
    (hArc : Pairwise (fun i j => arc i ∩ arc j = {a, b}))
    (hD : ∀ i, IsClosed (D i)) (hcover : d ⊆ ⋃ i, D i)
    (hpair : Pairwise (fun i j => D i ∩ D j ⊆ ⋃ k, arc k))
    (hcontact : ∀ i, D i ∩ (⋃ j, arc j) = arc (false, i.2) ∪ arc (true, i.1))
    (hdgraph : d ∩ (⋃ j, arc j) = u) (huw : u ∩ w = {c, e}) (k : Bool × Bool)
    (hw₀ : ∃ x ∈ d, x ∈ arc (false, k.2) ∧ x ∉ ({a, b} : Set X))
    (hw₁ : ∃ x ∈ d, x ∈ arc (true, k.1) ∧ x ∉ ({a, b} : Set X)) :
    d ⊆ D k ∧ u ⊆ arc (false, k.2) ∪ arc (true, k.1) ∧
      w \ {c, e} ⊆ D k \ (arc (false, k.2) ∪ arc (true, k.1)) := by
  have hsub := hd.subset_four_region_of_arc_witnesses arc D hArc hD hcover hpair
    hcontact (hdgraph.subset.trans subset_union_left) k hw₀ hw₁
  refine ⟨hsub, ?_, ?_⟩
  · intro x hx
    have hxgraph := hdgraph.symm.subset hx
    exact (hcontact k).subset ⟨hsub hxgraph.1, hxgraph.2⟩
  · intro x hx
    have hxd : x ∈ d := hd.1 (Or.inr hx.1)
    refine ⟨hsub hxd, ?_⟩
    intro hxrim
    have hxg := ((hcontact k).symm.subset hxrim).2
    exact hx.2 (huw.subset ⟨hdgraph.subset ⟨hxd, hxg⟩, hx.1⟩)

end Set
