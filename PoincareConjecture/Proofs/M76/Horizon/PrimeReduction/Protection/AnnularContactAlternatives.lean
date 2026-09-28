import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SourceCircleCuts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus
import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)

theorem exists_innermost_polygon_disk_in_region
    {ι : Type*} [Finite ι] (n : ι → ℕ) (P : ∀ i, Polygon P2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (U : Set P2) (hex : ∃ i, closure (P i).inside ⊆ U) :
    ∃ i, IsFinitePLBallPair P2 (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ⊆ U ∧
      closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
      Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) ∧
      ∀ j, i ≠ j → Disjoint (closure (P i).inside) ((P j).boundary ℝ) := by
  classical
  let I := {i : ι // closure (P i).inside ⊆ U}
  let : Nonempty I := ⟨⟨hex.choose, hex.choose_spec⟩⟩
  obtain ⟨i, hmin⟩ := Polygon.exists_innermost_closed_inside
    (fun i : I => n i) (fun i : I => P i) (fun i => hP i) (fun i => hi i)
    (fun i j hij => hdis (fun h => hij (Subtype.ext h)))
  have havoid (j : ι) (hij : i.val ≠ j) :
      Disjoint (closure (P i).inside) ((P j).boundary ℝ) := by
    rcases (P i).boundary_subset_inside_or_outside_of_disjoint (P j)
      (hP i) (hi i) (hP j) (hi j) (hdis hij) with hinside | houtside
    · have hsub := (P i).closure_inside_subset_inside_of_boundary_subset_inside (P j)
        (hP i) (hi i) (hP j) (hi j) hinside
      let k : I := ⟨j, hsub.trans (subset_closure.trans i.property)⟩
      exact hmin k (fun h => hij (congrArg Subtype.val h))
    · apply disjoint_left.mpr
      intro x hx hxj
      rw [(P i).closure_inside (hP i) (hi i)] at hx
      exact hx (houtside hxj)
  have heq : closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) =
      (P i).boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxall⟩
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hxall
      by_cases hij : i.val = j
      · exact hij.symm ▸ hxj
      · exact (disjoint_left.mp (havoid j hij) hx hxj).elim
    · intro x hx
      exact ⟨((P i).isFinitePLBallPair_closed_inside (hP i) (hi i)).1 hx,
        mem_iUnion.mpr ⟨i, hx⟩⟩
  refine ⟨i, (P i).isFinitePLBallPair_closed_inside (hP i) (hi i), i.property,
    heq, ?_, havoid⟩
  apply disjoint_left.mpr
  intro x hx hxall
  exact hx.1 (heq.subset ⟨subset_closure hx, hxall⟩)

theorem annular_polygon_family_disk_or_nested
    {ι : Type*} [Finite ι] (n : ι → ℕ) (P : ∀ i, Polygon P2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    {L d : ℝ} (hwidth : 2 * d < L)
    (hboundary : ∀ i x, x ∈ (P i).boundary ℝ → -d < depth L x ∧ depth L x < d) :
    (∃ i, IsFinitePLBallPair P2 (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ⊆ {x | -d < depth L x ∧ depth L x < d} ∧
      closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
      Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) ∧
      ∀ j, i ≠ j → Disjoint (closure (P i).inside) ((P j).boundary ℝ)) ∨
    ((∀ i, Dehn.annulusSquare L d ⊆ (P i).inside) ∧
      ∀ i j, i ≠ j → closure (P i).inside ⊆ (P j).inside ∨
        closure (P j).inside ⊆ (P i).inside) := by
  classical
  by_cases hex : ∃ i, closure (P i).inside ⊆ {x | -d < depth L x ∧ depth L x < d}
  · exact Or.inl (exists_innermost_polygon_disk_in_region n P hP hi hdis _ hex)
  · have hencl (i : ι) : Dehn.annulusSquare L d ⊆ (P i).inside := by
      exact (Dehn.Annuli.source_polygon_disk_or_enclosing (P i) (hP i) (hi i)
        (hboundary i)).2.2.resolve_right (fun h => hex ⟨i,h⟩)
    exact Or.inr ⟨hencl, fun i j hij =>
      Dehn.Annuli.enclosing_source_polygons_nested (P i) (P j)
        (hP i) (hi i) (hP j) (hi j) (hdis hij) hwidth (hencl i) (hencl j)⟩

theorem exists_adjacent_enclosing_polygon_annulus
    {ι : Type*} [Finite ι] [Nontrivial ι]
    (n : ι → ℕ) (P : ∀ i, Polygon P2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    {L d : ℝ} (hwidth : 2 * d < L)
    (hboundary : ∀ i x, x ∈ (P i).boundary ℝ → -d < depth L x ∧ depth L x < d)
    (hencl : ∀ i, Dehn.annulusSquare L d ⊆ (P i).inside) :
    ∃ i j, i ≠ j ∧ closure (P i).inside ⊆ (P j).inside ∧
      (closure (P j).inside \ (P i).inside) ⊆
        {x | -d < depth L x ∧ depth L x < d} ∧
      (closure (P j).inside \ (P i).inside) ∩ (⋃ k, (P k).boundary ℝ) =
        (P i).boundary ℝ ∪ (P j).boundary ℝ ∧
      ∃ H : squareAnnulus 8 1 ≃ₜ (closure (P j).inside \ (P i).inside : Set P2),
        H.IsFinitePL ∧
        (∀ z : squareAnnulus 8 1, depth 8 (z : P2) = -1 ↔
          (H z : P2) ∈ (P j).boundary ℝ) ∧
        (∀ z : squareAnnulus 8 1, depth 8 (z : P2) = 1 ↔
          (H z : P2) ∈ (P i).boundary ℝ) ∧
        ∃ U : Set P2, IsOpen U ∧ (closure (P j).inside \ (P i).inside) ⊆ U ∧
          U ∩ (⋃ k, (P k).boundary ℝ) = (P i).boundary ℝ ∪ (P j).boundary ℝ := by
  classical
  obtain ⟨i, hmin⟩ := Polygon.exists_innermost_closed_inside n P hP hi hdis
  let I := {j : ι // j ≠ i}
  let : Nonempty I := by
    obtain ⟨j,hji⟩ := exists_ne i
    exact ⟨⟨j,hji⟩⟩
  obtain ⟨j, hnext⟩ := Polygon.exists_innermost_closed_inside
    (fun j : I => n j) (fun j : I => P j) (fun j => hP j) (fun j => hi j)
    (fun j k hjk => hdis (fun h => hjk (Subtype.ext h)))
  have hij : i ≠ j.val := Ne.symm j.property
  have hnest : closure (P i).inside ⊆ (P j).inside := by
    rcases Dehn.Annuli.enclosing_source_polygons_nested (P i) (P j)
      (hP i) (hi i) (hP j) (hi j) (hdis hij) hwidth (hencl i) (hencl j) with h | h
    · exact h
    · obtain ⟨x,hx⟩ := ((P j).isConnected_boundary (hP j) (hi j)).nonempty
      exact (disjoint_left.mp (hmin j hij)
        (subset_closure (h (((P j).isFinitePLBallPair_closed_inside (hP j) (hi j)).1 hx)))
        hx).elim
  have hball (k : ι) := (P k).isFinitePLBallPair_closed_inside (hP k) (hi k)
  have hnot (k : ι) {x : P2} (hx : x ∈ (P k).boundary ℝ) : x ∉ (P k).inside := by
    intro hin
    exact hin.1 hx
  have hexact : (closure (P j).inside \ (P i).inside) ∩
      (⋃ k, (P k).boundary ℝ) = (P i).boundary ℝ ∪ (P j).boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx,hxf⟩
      obtain ⟨k,hxk⟩ := mem_iUnion.mp hxf
      by_cases hki : k = i
      · exact Or.inl (hki ▸ hxk)
      by_cases hkj : k = j.val
      · exact Or.inr (hkj ▸ hxk)
      let k' : I := ⟨k,hki⟩
      exact (disjoint_left.mp (hnext k' (fun heq => hkj
        (congrArg Subtype.val heq).symm)) hx.1 hxk).elim
    · rintro x (hxi | hxj)
      · exact ⟨⟨subset_closure (hnest ((hball i).1 hxi)), hnot i hxi⟩,
          mem_iUnion.mpr ⟨i,hxi⟩⟩
      · refine ⟨⟨(hball j).1 hxj, ?_⟩, mem_iUnion.mpr ⟨j,hxj⟩⟩
        intro hxi
        exact hnot j hxj (hnest (subset_closure hxi))
  refine ⟨i,j,hij,hnest,?_,hexact,?_⟩
  · rintro x ⟨hx,hxi⟩
    have hout := (Dehn.Annuli.source_polygon_disk_or_enclosing (P j)
      (hP j) (hi j) (hboundary j)).2.1 hx
    refine ⟨(_root_.Dehn.mem_interior_annulusSquare_iff L (-d) x).mp hout, ?_⟩
    apply lt_of_not_ge
    intro hh
    exact hxi (hencl i ((_root_.Dehn.mem_annulusSquare_iff L d x).mpr hh))
  · obtain ⟨H,hH,ho,hin⟩ := Dehn.exists_square_annulus_nested_polygons (P j) (P i)
      (hP j) (hi j) (hP i) (hi i) hnest (L := 8) (d := 1)
      (by norm_num) (by norm_num)
    let J := {k : ι // k ≠ i ∧ k ≠ j.val}
    let U := (⋃ k : J, (P k).boundary ℝ)ᶜ
    have hU : IsOpen U := (isClosed_iUnion_of_finite
      (fun k : J => (P k).isClosed_boundary)).isOpen_compl
    have hsub : (closure (P j).inside \ (P i).inside) ⊆ U := by
      intro x hx hxother
      obtain ⟨k,hxk⟩ := mem_iUnion.mp hxother
      exact disjoint_left.mp (hnext ⟨k,k.property.1⟩ (fun heq =>
        k.property.2 (congrArg Subtype.val heq).symm)) hx.1 hxk
    refine ⟨H,hH,ho,hin,U,hU,hsub,?_⟩
    apply Subset.antisymm
    · rintro x ⟨hxU,hxall⟩
      obtain ⟨k,hxk⟩ := mem_iUnion.mp hxall
      by_cases hki : k = i
      · exact Or.inl (hki ▸ hxk)
      by_cases hkj : k = j.val
      · exact Or.inr (hkj ▸ hxk)
      exact (hxU (mem_iUnion.mpr ⟨⟨k,hki,hkj⟩,hxk⟩)).elim
    · intro x hx
      have hxregion := hexact.symm.subset hx
      exact ⟨hsub hxregion.1,hxregion.2⟩

end PoincareConjecture.M76
