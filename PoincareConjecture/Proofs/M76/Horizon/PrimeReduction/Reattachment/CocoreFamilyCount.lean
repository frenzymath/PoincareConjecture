import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreComponentCount








set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem cocore_family_count_after_circle_exchange
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] [DecidableEq κ]
    (C : κ → Set E) (hC : ∀ i, IsClosed (C i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j)) (j : κ)
    (hpres : HasDisjointPolygonPresentation (⋃ i, C i))
    {n : ℕ} (L : Polygon E (n + 3))
    (hi : Function.Injective L) (he : L.HasSimplicialEdges) (hLC : L.boundary ℝ ⊆ C j)
    (hrem : IsCompact ((⋃ i, C i) \ L.boundary ℝ))
    (N : Bool → Set E) (hN : ∀ b, IsClosed (N b)) (hNd : Disjoint (N true) (N false))
    (hNC : ∀ b i, i ≠ j → Disjoint (N b) (C i))
    (hdelete : N true ∪ N false = C j \ L.boundary ℝ) :
    ∀ b, HasDisjointPolygonPresentation (⋃ i, Function.update C j (N b) i) ∧
      Nat.card (ConnectedComponents ↥(⋃ i, Function.update C j (N b) i)) <
        Nat.card (ConnectedComponents ↥(⋃ i, C i)) := by
  classical
  let U := ⋃ i : {i : κ // i ≠ j}, C i
  have hUc : IsClosed U := isClosed_iUnion_of_finite (fun i => hC i)
  have hUL : Disjoint U (L.boundary ℝ) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hdis i.property) hi (hLC hy)
  have hwhole : C j ∪ U = ⋃ i, C i := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact mem_iUnion_of_mem j hx
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion_of_mem i.val hi
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (mem_iUnion_of_mem ⟨i,hij⟩ hi)
  have hLN : L.boundary ℝ ⊆ ⋃ i, C i := fun _ hx => mem_iUnion_of_mem j (hLC hx)
  have hsplit : L.boundary ℝ ∪ ((⋃ i, C i) \ L.boundary ℝ) = ⋃ i, C i :=
    union_sdiff_cancel hLN
  have hprem := ((hsplit.symm ▸ hpres).closed_cut L.isClosed_boundary hrem.isClosed
    disjoint_sdiff_right).2
  intro b
  have hupdate : (⋃ i, Function.update C j (N b) i) = N b ∪ U := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · subst i
        exact Or.inl (by simpa only [Function.update_self] using hi)
      · exact Or.inr (mem_iUnion_of_mem ⟨i,hij⟩ (by
          simpa only [Function.update_of_ne hij] using hi))
    · rintro (hx | hx)
      · exact mem_iUnion_of_mem j (by simpa only [Function.update_self] using hx)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion_of_mem i.val (by simpa only [Function.update_of_ne i.property] using hi)
  have hpair : Disjoint (N b) (N (!b)) := by
    cases b
    · exact hNd.symm
    · exact hNd
  have hother : Disjoint U (N (!b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hNC (!b) i.val i.property) hy hi
  have hparts : (N b ∪ U) ∪ N (!b) = (⋃ i, C i) \ L.boundary ℝ := by
    have hNb : N b ∪ N (!b) = C j \ L.boundary ℝ := by
      cases b
      · simpa only [Bool.not_false,union_comm] using hdelete
      · exact hdelete
    rw [union_right_comm,hNb,← hwhole,union_sdiff_distrib]
    rw [hUL.sdiff_eq_left]
  have hcounts := cocore_component_counts_after_circle_surgery hpres L hi he hLN hrem
    ((hN b).union hUc) (hN (!b)) (hpair.union_left hother) hparts
  have hnewpres := (hparts.symm ▸ hprem).closed_cut ((hN b).union hUc) (hN (!b))
    (hpair.union_left hother)
  rw [hupdate]
  exact ⟨hnewpres.1,hcounts.2.1⟩

end PoincareConjecture.M76
