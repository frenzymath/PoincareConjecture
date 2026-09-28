import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.CappedBoundaryPartition










set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_raw_circle_boundary_count
    {X γ ρ κ : Type*} [TopologicalSpace X] [Finite γ] [Finite ρ] [Finite κ]
    {B F cap D : Set X} (P : γ → Set X) (rim : ρ → Set X) (S : κ → Set X)
    (hP : ∀ c, IsClosed (P c))
    (hPdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hPcover : (⋃ i, S i) ∩ B ⊆ ⋃ c, P c) (hPS : ∀ c, P c ⊆ ⋃ i, S i)
    (hS : ∀ i, IsClosed (S i)) (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hF : IsClosed F) (hFB : F ⊆ B) (hrim : ∀ j, IsConnected (rim j))
    (hrimdis : Pairwise fun j k => Disjoint (rim j) (rim k))
    (hrimcover : (⋃ j, rim j) = (⋃ i, S i) ∩ F)
    (i : κ) (V : Fin 2 → Set X) (hV : ∀ k, IsClosed (V k))
    (hVwhole : V 0 ∪ V 1 = S i) (hVinter : V 0 ∩ V 1 ⊆ cap)
    (hcap : IsClosed cap) (hcapF : Disjoint cap F)
    (c : γ) (hcontact : cap ∩ (⋃ i, S i) ⊆ P c)
    (a : ρ) (haP : rim a ⊆ P c)
    (hother : ∃ y ∈ P c ∩ F, y ∉ rim a)
    (repair : Fin 2) (haV : rim a ⊆ V repair)
    (hrepair : ∀ x ∈ rim a, connectedComponentIn ((V repair ∪ cap) ∩ B) x = D)
    (hDfront : D ∩ F = rim a) :
    ∃ (old : ρ → γ) (side : ρ → ({j : κ // j ≠ i} ⊕ Fin 2)) (point : ρ → X),
      (∀ j, rim j ⊆ P (old j) ∧ point j ∈ rim j) ∧
      side a = Sum.inr repair ∧
      (∀ j, rim j ⊆ Sum.elim (fun k : {j : κ // j ≠ i} => S k.val) V (side j)) ∧
      ∀ selected : Set ({j : κ // j ≠ i} ⊕ Fin 2),
        let retained := {j | side j ∈ selected}
        let family := Sum.elim (fun k : {j : κ // j ≠ i} => S k.val) (fun k => V k ∪ cap)
        let label := fun j => (side j, connectedComponentIn (family (side j) ∩ B) (point j))
        retained.ncard - (label '' retained).ncard < Nat.card ρ - (Set.range old).ncard := by
  classical
  have hrimsub (j : ρ) : rim j ⊆ (⋃ i, S i) ∩ F :=
    (subset_iUnion rim j).trans hrimcover.subset
  have hold (j : ρ) : ∃ c, rim j ⊆ P c := by
    obtain ⟨c,hc,_⟩ := (hrim j).exists_unique_subset_finite_disjoint_closed P hP hPdis
      (fun x hx => hPcover ⟨(hrimsub j hx).1,hFB (hrimsub j hx).2⟩)
    exact ⟨c,hc⟩
  choose old hold using hold
  have hoa : old a = c := by
    obtain ⟨x,hx⟩ := (hrim a).nonempty
    by_contra hn
    exact disjoint_left.mp (hPdis hn) (hold a hx) (haP hx)
  obtain ⟨y,hy,hyoff⟩ := hother
  obtain ⟨b,hyb⟩ := mem_iUnion.mp (hrimcover.symm.subset ⟨hPS c hy.1,hy.2⟩)
  have hab : a ≠ b := by
    intro heq
    exact hyoff (heq.symm ▸ hyb)
  have hob : old b = c := by
    by_contra hn
    exact disjoint_left.mp (hPdis hn) (hold b hyb) hy.1
  let R : ({j : κ // j ≠ i} ⊕ Fin 2) → Set X :=
    Sum.elim (fun k => S k.val) V
  let caps : ({j : κ // j ≠ i} ⊕ Fin 2) → Set X :=
    Sum.elim (fun _ => ∅) (fun _ => cap)
  have hVS (k : Fin 2) : V k ⊆ S i := by
    fin_cases k
    · exact subset_union_left.trans hVwhole.subset
    · exact subset_union_right.trans hVwhole.subset
  have hRclosed (k) : IsClosed (R k ∩ F) := by
    cases k with
    | inl k => exact (hS k.val).inter hF
    | inr k => exact (hV k).inter hF
  have hRdis : Pairwise fun k l => Disjoint (R k ∩ F) (R l ∩ F) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro x ⟨hx,hxF⟩ ⟨hy,hyF⟩
    cases k with
    | inl k =>
      cases l with
      | inl l => exact disjoint_left.mp (hSdis (by intro h; exact hkl (by simpa [Subtype.ext_iff] using h))) hx hy
      | inr l => exact disjoint_left.mp (hSdis k.property) hx (hVS l hy)
    | inr k =>
      cases l with
      | inl l => exact disjoint_left.mp (hSdis l.property) hy (hVS k hx)
      | inr l =>
        have hne : k ≠ l := fun h => hkl (congrArg Sum.inr h)
        have hxcap : x ∈ cap := by
          fin_cases k <;> fin_cases l
          · exact (hne rfl).elim
          · exact hVinter ⟨hx,hy⟩
          · exact hVinter ⟨hy,hx⟩
          · exact (hne rfl).elim
        exact disjoint_left.mp hcapF hxcap hxF
  have hRcover : (⋃ i, S i) ∩ F ⊆ ⋃ k, R k ∩ F := by
    rintro x ⟨hx,hxF⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · subst j
      rcases hVwhole.symm.subset hj with hx | hx
      · exact mem_iUnion.mpr ⟨Sum.inr 0,hx,hxF⟩
      · exact mem_iUnion.mpr ⟨Sum.inr 1,hx,hxF⟩
    · exact mem_iUnion.mpr ⟨Sum.inl ⟨j,hji⟩,hj,hxF⟩
  obtain ⟨side,point,hpoint,hside,hcount⟩ := exists_capped_boundary_partition_strict_decrease
    P rim old R caps hP hPdis hPcover hPS c (by intro k; cases k <;> simp [caps,hcap])
    (by intro k; cases k with
      | inl k => simp [caps]
      | inr k => exact hcontact) hrim
    (fun j x hx => ⟨⟨(hrimsub j hx).1,hFB (hrimsub j hx).2⟩,(hrimsub j hx).2⟩)
    hold hrimdis hRclosed (by intro k; cases k with
      | inl k => exact subset_iUnion S k.val
      | inr k => exact (hVS k).trans (subset_iUnion S i)) hRcover hRdis hab
    (hoa.trans hob.symm) (Sum.inr repair) haV hrepair hDfront
  refine ⟨old,side,point,fun j => ⟨hold j,(hpoint j).1⟩,hside,fun j => (hpoint j).2,?_⟩
  intro selected
  have hfamily (k) : R k ∪ caps k =
      Sum.elim (fun j : {j : κ // j ≠ i} => S j.val) (fun j => V j ∪ cap) k := by
    cases k <;> simp [R,caps]
  simpa only [hfamily] using hcount selected

end PoincareConjecture.M76
