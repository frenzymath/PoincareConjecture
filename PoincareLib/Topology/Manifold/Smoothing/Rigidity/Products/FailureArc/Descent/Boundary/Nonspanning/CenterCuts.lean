import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.TwoProperArcCuts
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

/-! # The annulus piece cut out by two nonspanning boundary arcs

The two arcs cut the filled outer disk into three disks. Connectedness
places the untouched inner disk in exactly one of the pieces, strictly
inside it. Removing that inner disk constructs the retained annulus.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_two_outer_boundary_arc_annulus_cut
    {S T W Z : Set P2} {a b c d : P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hZ : IsFinitePLBallPair ℝ Z {c, d})
    (ha : a ∈ frontier T) (hb : b ∈ frontier T)
    (hc : c ∈ frontier T) (hd : d ∈ frontier T)
    (hab : a ≠ b) (hcd : c ≠ d) (hWZ : Disjoint W Z)
    (hproperW : W \ {a, b} ⊆ interior T)
    (hproperZ : Z \ {c, d} ⊆ interior T)
    (hWS : Disjoint W S) (hZS : Disjoint Z S) :
    ∃ A B C D : Set P2,
      IsFinitePLBallPair P2 A ((A ∩ frontier T) ∪ W) ∧
      IsFinitePLBallPair P2 B (((B ∩ frontier T) ∪ W) ∪ Z) ∧
      IsFinitePLBallPair P2 C ((C ∩ frontier T) ∪ Z) ∧
      (A ∪ B) ∪ C = T ∧ A ∩ B = W ∧ B ∩ C = Z ∧ Disjoint A C ∧
      (D = A ∨ D = B ∨ D = C) ∧ S ⊆ interior D ∧
      (∀ E ∈ ({A, B, C} : Set (Set P2)), E ≠ D → Disjoint E S) ∧
      ∃ H : squareAnnulus 8 1 ≃ₜ (D \ interior S : Set P2), H.IsFinitePL ∧
        (∀ z : squareAnnulus 8 1,
          depth 8 (z : P2) = -1 ↔ (H z : P2) ∈ frontier D) ∧
        ∀ z : squareAnnulus 8 1,
          depth 8 (z : P2) = 1 ↔ (H z : P2) ∈ frontier S := by
  have hTW : W \ {a, b} ⊆ T \ frontier T := by
    rw [← hT.interior_eq_sdiff_of_finrank_eq rfl]
    exact hproperW
  have hTZ : Z \ {c, d} ⊆ T \ frontier T := by
    rw [← hT.interior_eq_sdiff_of_finrank_eq rfl]
    exact hproperZ
  obtain ⟨A, B, C, hA, hB, hC, hcover, hAB, hBC, hAC⟩ :=
    exists_two_proper_arc_cuts hT hW hZ ha hb hc hd hab hcd hWZ hTW hTZ
  have hAW : A ∩ (B ∪ C) = W := by
    rw [inter_union_distrib_left, hAB, (show A ∩ C = ∅ from hAC.eq_bot), union_empty]
  have hside : S ⊆ A ∨ S ⊆ B ∨ S ⊆ C := by
    have hsub : S ⊆ A ∪ (B ∪ C) := by
      rw [← union_assoc, hcover]
      exact hST.trans interior_subset
    rcases isPreconnected_subset_one_cut_piece hS.isConnected.isPreconnected
      hA.isCompact.isClosed (hB.isCompact.isClosed.union hC.isCompact.isClosed)
      hsub hAW hWS.symm with hSA | hSBC
    · exact Or.inl hSA
    · exact Or.inr (isPreconnected_subset_one_cut_piece hS.isConnected.isPreconnected
        hB.isCompact.isClosed hC.isCompact.isClosed hSBC hBC hZS.symm)
  have havoid : Disjoint S (frontier T ∪ (W ∪ Z)) := by
    refine disjoint_left.mpr ?_
    intro x hx
    rintro (hxT | hxW | hxZ)
    · exact hxT.2 (hST hx)
    · exact disjoint_left.mp hWS hxW hx
    · exact disjoint_left.mp hZS hxZ hx
  have hinside (E Q : Set P2) (hE : IsFinitePLBallPair P2 E Q)
      (hQ : Q ⊆ frontier T ∪ (W ∪ Z)) (hSE : S ⊆ E) : S ⊆ interior E := by
    rw [hE.interior_eq_sdiff_of_finrank_eq rfl]
    exact fun x hx => ⟨hSE hx, fun hq => disjoint_left.mp havoid hx (hQ hq)⟩
  have hAf : IsFinitePLBallPair P2 A (frontier A) :=
    (hA.frontier_eq_of_finrank_eq rfl).symm ▸ hA
  have hBf : IsFinitePLBallPair P2 B (frontier B) :=
    (hB.frontier_eq_of_finrank_eq rfl).symm ▸ hB
  have hCf : IsFinitePLBallPair P2 C (frontier C) :=
    (hC.frontier_eq_of_finrank_eq rfl).symm ▸ hC
  have hAQ : (A ∩ frontier T) ∪ W ⊆ frontier T ∪ (W ∪ Z) := by
    rintro x (hx | hx)
    · exact Or.inl hx.2
    · exact Or.inr (Or.inl hx)
  have hBQ : ((B ∩ frontier T) ∪ W) ∪ Z ⊆ frontier T ∪ (W ∪ Z) := by
    rintro x ((hx | hx) | hx)
    · exact Or.inl hx.2
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have hCQ : (C ∩ frontier T) ∪ Z ⊆ frontier T ∪ (W ∪ Z) := by
    rintro x (hx | hx)
    · exact Or.inl hx.2
    · exact Or.inr (Or.inr hx)
  have hother (D : Set P2) (hSD : S ⊆ D) (hD : D = A ∨ D = B ∨ D = C) :
      ∀ E ∈ ({A, B, C} : Set (Set P2)), E ≠ D → Disjoint E S := by
    intro E hE hne
    have hE' : E = A ∨ E = B ∨ E = C := by simpa only [mem_insert_iff, mem_singleton_iff] using hE
    apply disjoint_left.mpr
    intro x hxE hxS
    have hxD := hSD hxS
    rcases hD with rfl | rfl | rfl <;> rcases hE' with rfl | rfl | rfl
    · exact hne rfl
    · exact disjoint_left.mp hWS (hAB.subset ⟨hxD, hxE⟩) hxS
    · exact disjoint_left.mp hAC hxD hxE
    · exact disjoint_left.mp hWS (hAB.subset ⟨hxE, hxD⟩) hxS
    · exact hne rfl
    · exact disjoint_left.mp hZS (hBC.subset ⟨hxD, hxE⟩) hxS
    · exact disjoint_left.mp hAC hxE hxD
    · exact disjoint_left.mp hZS (hBC.subset ⟨hxE, hxD⟩) hxS
    · exact hne rfl
  have selected : ∃ D : Set P2, (D = A ∨ D = B ∨ D = C) ∧
      IsFinitePLBallPair P2 D (frontier D) ∧ S ⊆ interior D := by
    rcases hside with hSA | hSB | hSC
    · exact ⟨A, Or.inl rfl, hAf, hinside A _ hA hAQ hSA⟩
    · exact ⟨B, Or.inr (Or.inl rfl), hBf, hinside B _ hB hBQ hSB⟩
    · exact ⟨C, Or.inr (Or.inr rfl), hCf, hinside C _ hC hCQ hSC⟩
  obtain ⟨D, hD, hDf, hSD⟩ := selected
  obtain ⟨H, hH, hout, hin⟩ := exists_square_annulus_nested_disks hS hDf hSD
    (show (0 : ℝ) < 1 by norm_num) (show (2 : ℝ) * 1 < 8 by norm_num)
  exact ⟨A, B, C, D, hA, hB, hC, hcover, hAB, hBC, hAC, hD, hSD,
    hother D (hSD.trans interior_subset) hD, H, hH, hout, hin⟩

end PoincareMT.M76.Dehn
