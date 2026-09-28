import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.ReturningDisk
import Mathlib.Order.WellFoundedSet








set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_outermost_returning_arc_disk
    {κ : Type*} [Finite κ] [Nonempty κ]
    {S T : Set P2} (W : κ → Set P2) (a b : κ → P2)
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i})
    (hab : ∀ i, a i ≠ b i)
    (ha : ∀ i, a i ∈ frontier T) (hb : ∀ i, b i ∈ frontier T)
    (hproper : ∀ i, W i \ {a i, b i} ⊆ interior T)
    (hWS : ∀ i, Disjoint (W i) S)
    (hdis : Pairwise (fun i j ↦ Disjoint (W i) (W j))) :
    ∃ (i : κ) (D B U V : Set P2),
      IsFinitePLBallPair ℝ U {a i, b i} ∧ IsFinitePLBallPair ℝ V {a i, b i} ∧
      U ∪ V = frontier T ∧ U ∩ V = {a i, b i} ∧
      IsFinitePLBallPair P2 D (U ∪ W i) ∧
      IsFinitePLBallPair P2 B (W i ∪ V) ∧
      D ∪ B = T ∧ D ∩ B = W i ∧
      D ∩ frontier T = U ∧ B ∩ frontier T = V ∧
      S ⊆ interior B ∧ Disjoint D S ∧ D ⊆ T \ S ∧
      (∀ j, j ≠ i → Disjoint D (W j)) ∧
      ∀ K : Set P2, IsPreconnected K → K ⊆ T → Disjoint K (W i) →
        (K ∩ S).Nonempty → Disjoint D K := by
  classical
  choose D B U V hU hV hUV hUVi hD hB hcover hinter hDU hBV hSin hDS hDT hkeep
    using fun i ↦ exists_returning_arc_disk hS hT hST (hW i) (hab i)
      (ha i) (hb i) (hproper i) (hWS i)
  obtain ⟨d, hd⟩ := (finite_range D).isPWO.exists_minimal (range_nonempty D)
  obtain ⟨i, rfl⟩ := hd.1
  have havoid (j : κ) (hji : j ≠ i) : Disjoint (D i) (W j) := by
    have hWT : W j ⊆ T := by
      intro x hx
      by_cases hends : x ∈ ({a j, b j} : Set P2)
      · rcases hends with rfl | rfl
        · exact hT.1 (ha j)
        · exact hT.1 (hb j)
      · exact interior_subset (hproper j ⟨hx, hends⟩)
    rcases isPreconnected_subset_one_cut_piece (hW j).isConnected.isPreconnected
        (hD i).isCompact.isClosed (hB i).isCompact.isClosed
        (hWT.trans (hcover i).symm.subset) (hinter i) (hdis hji) with hjD | hjB
    · have hBiWj : Disjoint (B i) (W j) := by
        refine disjoint_left.mpr fun x hxB hxW ↦ ?_
        exact disjoint_left.mp (hdis hji) hxW ((hinter i).subset ⟨hjD hxW, hxB⟩)
      have hBiBj : B i ⊆ B j := by
        have hBiT : B i ⊆ T := subset_union_right.trans (hcover i).subset
        rcases isPreconnected_subset_one_cut_piece (hB i).isConnected.isPreconnected
            (hD j).isCompact.isClosed (hB j).isCompact.isClosed
            (hBiT.trans (hcover j).symm.subset) (hinter j) hBiWj with hiD | hiB
        · obtain ⟨x, hxS⟩ := hS.isConnected.nonempty
          exact (disjoint_left.mp (hDS j)
            (hiD (interior_subset (hSin i hxS))) hxS).elim
        · exact hiB
      have hjDi : D j ⊆ D i := by
        intro x hxDj
        by_contra hxDi
        have hxBi : x ∈ B i := ((hcover i).symm.subset (hDT j hxDj).1).resolve_left hxDi
        exact hxDi (hjD ((hinter j).subset ⟨hxDj, hBiBj hxBi⟩))
      have heq : D i = D j := Subset.antisymm (hd.2 (mem_range_self j) hjDi) hjDi
      have haiW : a i ∈ W i := (hW i).1 (by simp)
      have haiD : a i ∈ D j := heq ▸ ((hinter i).symm.subset haiW).1
      have haiB : a i ∈ B j := hBiBj ((hinter i).symm.subset haiW).2
      exact (disjoint_left.mp (hdis hji) ((hinter j).subset ⟨haiD, haiB⟩) haiW).elim
    · exact disjoint_left.mpr fun x hxD hxW ↦
        disjoint_left.mp (hdis hji) hxW ((hinter i).subset ⟨hxD, hjB hxW⟩)
  exact ⟨i, D i, B i, U i, V i, hU i, hV i, hUV i, hUVi i, hD i, hB i,
    hcover i, hinter i, hDU i, hBV i, hSin i, hDS i, hDT i, havoid, hkeep i⟩

end PoincareConjecture.M76.Dehn.Annuli
