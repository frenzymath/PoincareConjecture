import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Polygons.FinitePLReturningBigon
import PoincareConjecture.Proofs.M76.PrimeReduction.InnermostReturningBigon
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.InnermostReturningContacts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ))

theorem exists_innermost_returning_disk_in_seed_strip
    {ι : Type*} [Finite ι] (W : ι → Set V) (a b : ι → V)
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i})
    (hab : ∀ i, (a i).1 < (b i).1)
    (hup : ∀ i x, x ∈ W i → 0 ≤ x.2)
    (haxis : ∀ i, W i ∩ Z = {a i, b i})
    (hdis : Pairwise fun i j => Disjoint (W i) (W j))
    (seed : ι) {C : Set V} (hC : Convex ℝ C) (hseed : W seed ⊆ C) :
    ∃ (i : ι) (B : Set V), IsFinitePLBallPair V B (W i ∪ segment ℝ (a i) (b i)) ∧
      IsCompact B ∧ B ⊆ C ∧ B ∩ Z = segment ℝ (a i) (b i) ∧
      B ∩ (⋃ j, W j) = W i ∧
      (⋃ j, W j) ∩ segment ℝ (a i) (b i) = {a i, b i} ∧
      ∃ (n : ℕ) (P : Polygon V (n + 3)), P.HasSimplicialEdges ∧ Function.Injective P ∧
        (∀ j, 0 ≤ (P j).2) ∧ P.boundary ℝ = W i ∪ segment ℝ (a i) (b i) ∧
        B = closure P.inside := by
  classical
  have hne (i : ι) : a i ≠ b i := fun h => (hab i).ne (congrArg Prod.fst h)
  choose n P hP hi hPu hboundary hball hcompact hbase hcontain using
    fun i => exists_finite_pl_returning_bigon (hW i) (hne i) (hup i) (haxis i)
  let J := {i : ι // (P i).inside ⊆ (P seed).inside}
  have : Nonempty J := ⟨⟨seed, Subset.rfl⟩⟩
  obtain ⟨s, hs⟩ := (finite_range (fun i : J => (P i.val).inside)).isPWO.exists_minimal
    (range_nonempty (fun i : J => (P i.val).inside))
  obtain ⟨i, rfl⟩ := hs.1
  have havoid (j : ι) : Disjoint (P i.val).inside ((P j).boundary ℝ) := by
    by_cases hij : i.val = j
    · subst j
      exact disjoint_left.mpr fun _ hx hb => hx.1 hb
    rcases (P i.val).returning_inside_subset_or_disjoint (P j) (hP i.val) (hi i.val)
        (hP j) (hi j) (hPu i.val) (hboundary i.val) (hboundary j)
        (haxis i.val) (haxis j) (hW j) (hdis hij) with hsub | hd
    · let j' : J := ⟨j, hsub.trans i.property⟩
      have heq : (P i.val).inside = (P j).inside :=
        Subset.antisymm (hs.2 (mem_range_self j') hsub) hsub
      have hbound : (P i.val).boundary ℝ = (P j).boundary ℝ := by
        rw [← (P i.val).frontier_inside (hP i.val) (hi i.val),
          ← (P j).frontier_inside (hP j) (hi j), heq]
      obtain ⟨x, hxW, hxends⟩ := (hW j).sdiff_nonempty
      have hxP : x ∈ (P i.val).boundary ℝ := by
        rw [hbound, hboundary j]
        exact Or.inl hxW
      rcases hboundary i.val ▸ hxP with hxWi | hxseg
      · exact (disjoint_left.mp (hdis hij) hxWi hxW).elim
      · have haZ : a i.val ∈ Z := ((haxis i.val).symm.subset (by simp)).2
        have hbZ : b i.val ∈ Z := ((haxis i.val).symm.subset (by simp)).2
        exact (hxends ((haxis j).subset
          ⟨hxW, Polygon.segment_subset_returning_axis haZ hbZ hxseg⟩)).elim
    · exact hd
  let D : Set V := univ ×ˢ Ici 0
  have hDfront : frontier D = Z := by
    dsimp [D]
    rw [frontier_univ_prod_eq, frontier_Ici]
    ext x
    simp
  have hWD (j : ι) : W j ⊆ D := fun x hx => ⟨mem_univ _, hup j x hx⟩
  have hBD : closure (P i.val).inside ⊆ D :=
    hcontain i.val D (convex_univ.prod (convex_Ici _)) (hWD i.val)
  have haZ : a i.val ∈ Z := ((haxis i.val).symm.subset (by simp)).2
  have hbZ : b i.val ∈ Z := ((haxis i.val).symm.subset (by simp)).2
  have hcontacts : (⋃ j, W j) ∩ segment ℝ (a i.val) (b i.val) = {a i.val, b i.val} := by
    apply Subset.antisymm
    · rintro q ⟨hqW, hqseg⟩
      obtain ⟨j, hqj⟩ := mem_iUnion.mp hqW
      have hq0 : q.2 = 0 := Polygon.segment_subset_returning_axis haZ hbZ hqseg
      by_cases hji : j = i.val
      · subst j
        exact (haxis i.val).subset ⟨hqj, hq0⟩
      have hd := hdis (Ne.symm hji)
      have hqa : q ≠ a i.val := fun h => disjoint_left.mp hd
        (h.symm ▸ (hW i.val).1 (by simp)) hqj
      have hqb : q ≠ b i.val := fun h => disjoint_left.mp hd
        (h.symm ▸ (hW i.val).1 (by simp)) hqj
      have hqIcc : q.1 ∈ Icc (a i.val).1 (b i.val).1 := by
        rw [Polygon.returning_axis_segment haZ hbZ (hab i.val).le] at hqseg
        exact hqseg.1
      have hqstrict : q.1 ∈ Ioo (a i.val).1 (b i.val).1 := by
        refine ⟨lt_of_le_of_ne hqIcc.1 ?_, lt_of_le_of_ne hqIcc.2 ?_⟩
        · exact fun h => hqa (Prod.ext h.symm (hq0.trans haZ.symm))
        · exact fun h => hqb (Prod.ext h (hq0.trans hbZ.symm))
      obtain ⟨hin, _, _, _⟩ := (P i.val).interval_trapped_of_returning_base_contact
        (hP i.val) (hi i.val) (hPu i.val) (hboundary i.val) (hW i.val) (haxis i.val)
        (hW j) (by rw [hDfront]; exact haxis j) (hWD j)
        (fun _ hx => hx.2) (fun x hx => hDfront.symm ▸ hx.2) hBD hd hqj hq0 hqstrict
      obtain ⟨x, hx⟩ := (hW j).sdiff_nonempty
      exact (disjoint_left.mp (havoid j) (hin hx)
        ((hboundary j).symm.subset (Or.inl hx.1))).elim
    · intro x hx
      refine ⟨mem_iUnion.mpr ⟨i.val, (hW i.val).1 hx⟩, ?_⟩
      rcases hx with hxa | hxb
      · rw [hxa]
        exact left_mem_segment ℝ _ _
      · rw [hxb]
        exact right_mem_segment ℝ _ _
  refine ⟨i.val, closure (P i.val).inside, hball i.val, hcompact i.val,
    (closure_mono i.property).trans (hcontain seed C hC hseed), hbase i.val, ?_, hcontacts,
    n i.val, P i.val, hP i.val, hi i.val, hPu i.val, hboundary i.val, rfl⟩
  apply Subset.antisymm
  · rintro x ⟨hxB, hxW⟩
    rw [closure_eq_self_union_frontier, (P i.val).frontier_inside (hP i.val) (hi i.val)] at hxB
    rcases hxB with hxin | hxfront
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxW
      exact (disjoint_left.mp (havoid j) hxin
        ((hboundary j).symm.subset (Or.inl hxj))).elim
    · rcases hboundary i.val ▸ hxfront with hxWi | hxseg
      · exact hxWi
      · exact (hW i.val).1 (hcontacts.subset ⟨hxW, hxseg⟩)
  · intro x hx
    exact ⟨(hball i.val).1 (Or.inl hx), mem_iUnion.mpr ⟨i.val, hx⟩⟩

end PoincareConjecture.M76.Dehn
