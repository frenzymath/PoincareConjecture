import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedShellSides
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)



structure NestedShellDissection (S T : Set P2) where
  x : P2
  y : P2
  a : P2
  b : P2
  outer : Fin 2 → Set P2
  inner : Fin 2 → Set P2
  left : Set P2
  right : Set P2
  disk : Fin 2 → Set P2
  outer_ball : ∀ j, IsFinitePLBallPair ℝ (outer j) {x, y}
  inner_ball : ∀ j, IsFinitePLBallPair ℝ (inner j) {a, b}
  left_ball : IsFinitePLBallPair ℝ left {x, a}
  right_ball : IsFinitePLBallPair ℝ right {y, b}
  xy_ne : x ≠ y
  ab_ne : a ≠ b
  xa_ne : x ≠ a
  yb_ne : y ≠ b
  outer_cover : outer 0 ∪ outer 1 = frontier T
  inner_cover : inner 0 ∪ inner 1 = frontier S
  outer_inter : outer 0 ∩ outer 1 = {x, y}
  inner_inter : inner 0 ∩ inner 1 = {a, b}
  cross_disjoint : ∀ j, Disjoint (outer j) (inner j)
  sides_disjoint : Disjoint left right
  outer_left : ∀ j, outer j ∩ left = {x}
  outer_right : ∀ j, outer j ∩ right = {y}
  inner_left : ∀ j, inner j ∩ left = {a}
  inner_right : ∀ j, inner j ∩ right = {b}
  disk_ball : ∀ j, IsFinitePLBallPair P2 (disk j)
    ((outer j ∪ inner j) ∪ (left ∪ right))
  disk_cover : disk 0 ∪ disk 1 = T \ interior S
  disk_inter : disk 0 ∩ disk 1 = left ∪ right

private theorem shell_half_complement {S sq A U W L R : Set P2} {a b : P2}
    (hS : IsFinitePLBallPair P2 S sq)
    (hA : IsFinitePLBallPair P2 A (U ∪ ((L ∪ W) ∪ R)))
    (hD : IsFinitePLBallPair P2 (S ∩ A) (W ∪ (sq ∩ A)))
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hu : IsFinitePLBallPair ℝ (sq ∩ A) {a, b}) (hab : a ≠ b)
    (hproper : (sq ∩ A) \ {a, b} ⊆ A \ (U ∪ ((L ∪ W) ∪ R)))
    (hUS : Disjoint U S) (hLS : L ∩ S = {a}) (hRS : R ∩ S = {b})
    (hWS : W ⊆ S) (hLa : a ∈ L) (hRb : b ∈ R) :
    IsFinitePLBallPair P2 (A \ interior S) (((U ∪ (sq ∩ A)) ∪ (L ∪ R))) := by
  obtain ⟨V, _, hcover, hinter, hball, _⟩ :=
    hA.exists_boundary_attached_disk_complement hD inter_subset_right hW
      (fun z hz ↦ Or.inr (Or.inl (Or.inr hz))) hu hab hproper
  have hVL : V = (U ∪ L) ∪ R := by
    ext z
    constructor
    · intro hz
      rcases hcover.subset (Or.inr hz) with hzU | (hzL | hzW) | hzR
      · exact Or.inl (Or.inl hzU)
      · exact Or.inl (Or.inr hzL)
      · rcases hinter.subset ⟨hzW, hz⟩ with rfl | rfl
        · exact Or.inl (Or.inr hLa)
        · exact Or.inr hRb
      · exact Or.inr hzR
    · intro hz
      have hzrim : z ∈ U ∪ ((L ∪ W) ∪ R) := by
        rcases hz with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr h)
      rcases hcover.symm.subset hzrim with hzW | hzV
      · have hends : z ∈ ({a, b} : Set P2) := by
          rcases hz with (h | h) | h
          · exact (disjoint_left.mp hUS h (hWS hzW)).elim
          · exact Or.inl (hLS.subset ⟨h, hWS hzW⟩)
          · exact Or.inr (hRS.subset ⟨h, hWS hzW⟩)
        exact (hinter.symm.subset hends).2
      · exact hzV
  have hset : A \ ((S ∩ A) \ (sq ∩ A)) = A \ interior S := by
    rw [hS.interior_eq_sdiff_of_finrank_eq rfl]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hset, hVL] at hball
  convert hball using 1
  ext z
  simp only [mem_union, mem_inter_iff]
  tauto



theorem exists_nested_shell_dissection {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T))
    (hST : S ⊆ interior T) : Nonempty (NestedShellDissection S T) := by
  obtain ⟨a, b, x, y, L, W, R, ha, hb, hab, hx, hy, hxy, hL, hW, hR,
    hZ, hWS, hWq, hWp, hLS, hRS, hLR, hZS, hZp⟩ :=
    exists_nested_shell_arc hS hS.isCompact
      (hS.isConnected_interior_of_finrank_eq rfl).nonempty hT.isCompact hST
  have hST' : S ⊆ T \ frontier T := by
    simpa only [hT.interior_eq_sdiff_of_finrank_eq rfl] using hST
  obtain ⟨A, B, U, V, u, v, hA, hB, hAB, hAiB, hAU, hBV,
    hU, hV, hUV, hUiV, hu, hv, huv, huiv, huA, hvB, hSA, hSB, hup, hvp⟩ :=
    exists_nested_disk_cut_halves hS hT hST' hW hZ hab hxy ha hb hx hy hWp hZp hWS hZS
  have haS := hS.1 ha
  have hbS := hS.1 hb
  have hxS : x ∉ S := fun h ↦ (hST' h).2 hx
  have hyS : y ∉ S := fun h ↦ (hST' h).2 hy
  have hxL : x ∈ L := hL.1 (Or.inl rfl)
  have haL : a ∈ L := hL.1 (Or.inr rfl)
  have hbR : b ∈ R := hR.1 (Or.inl rfl)
  have hyR : y ∈ R := hR.1 (Or.inr rfl)
  have hLa : L ∩ frontier S = {a} := by
    apply Subset.antisymm
    · exact fun z hz ↦ hLS.subset ⟨hz.1, hS.1 hz.2⟩
    · rintro z rfl
      exact ⟨haL, ha⟩
  have hRb : R ∩ frontier S = {b} := by
    apply Subset.antisymm
    · exact fun z hz ↦ hRS.subset ⟨hz.1, hS.1 hz.2⟩
    · rintro z rfl
      exact ⟨hbR, hb⟩
  have hLx : L ∩ frontier T = {x} := by
    apply Subset.antisymm
    · intro z hz
      have he : z ∈ ({x, y} : Set P2) := by
        by_contra hn
        exact (hZp ⟨Or.inl (Or.inl hz.1), hn⟩).2 hz.2
      rcases he with rfl | rfl
      · rfl
      · exact (disjoint_left.mp hLR hz.1 hyR).elim
    · rintro z rfl
      exact ⟨hxL, hx⟩
  have hRy : R ∩ frontier T = {y} := by
    apply Subset.antisymm
    · intro z hz
      have he : z ∈ ({x, y} : Set P2) := by
        by_contra hn
        exact (hZp ⟨Or.inr hz.1, hn⟩).2 hz.2
      rcases he with rfl | rfl
      · exact (disjoint_left.mp hLR hxL hz.1).elim
      · rfl
    · rintro z rfl
      exact ⟨hyR, hy⟩
  have hUS : Disjoint U S := disjoint_left.mpr fun z hz hs ↦
    (hST' hs).2 (hUV.subset (Or.inl hz))
  have hVS : Disjoint V S := disjoint_left.mpr fun z hz hs ↦
    (hST' hs).2 (hUV.subset (Or.inr hz))
  have hAball := shell_half_complement hS hA (huA ▸ hSA) hW (huA ▸ hu)
    hab (huA ▸ hup) hUS hLS hRS hWS haL hbR
  have hB' : IsFinitePLBallPair P2 B (V ∪ ((L ∪ W) ∪ R)) := by
    simpa only [union_comm] using hB
  have hvp' : (frontier S ∩ B) \ {a, b} ⊆ B \ (V ∪ ((L ∪ W) ∪ R)) := by
    simpa only [hvB, union_comm] using hvp
  have hBball := shell_half_complement hS hB' (hvB ▸ hSB) hW (hvB ▸ hv)
    hab hvp' hVS hLS hRS hWS haL hbR
  have hside (q r : Set P2) (hq : q ⊆ r) (p : P2) (hp : p ∈ q)
      (C : Set P2) (hC : C ∩ r = {p}) : q ∩ C = {p} := by
    apply Subset.antisymm
    · exact fun z hz ↦ hC.subset ⟨hz.2, hq hz.1⟩
    · rintro z rfl
      exact ⟨hp, (hC.symm.subset rfl).1⟩
  refine ⟨{
    x := x, y := y, a := a, b := b
    outer := ![U, V], inner := ![u, v], left := L, right := R
    disk := ![A \ interior S, B \ interior S]
    outer_ball := ?_, inner_ball := ?_, left_ball := hL
    right_ball := by simpa only [pair_comm] using hR
    xy_ne := hxy, ab_ne := hab
    xa_ne := fun h ↦ hxS (h ▸ haS), yb_ne := fun h ↦ hyS (h ▸ hbS)
    outer_cover := hUV, inner_cover := huv, outer_inter := hUiV, inner_inter := huiv
    cross_disjoint := ?_, sides_disjoint := hLR
    outer_left := ?_, outer_right := ?_, inner_left := ?_, inner_right := ?_
    disk_ball := ?_, disk_cover := ?_, disk_inter := ?_ }⟩
  · intro j; fin_cases j <;> assumption
  · intro j; fin_cases j <;> assumption
  · intro j; fin_cases j
    · exact hUS.mono_right (fun z hz ↦ hS.1 (huv.subset (Or.inl hz)))
    · exact hVS.mono_right (fun z hz ↦ hS.1 (huv.subset (Or.inr hz)))
  · intro j; fin_cases j
    · exact hside U _ (subset_union_left.trans hUV.subset) x (hU.1 (Or.inl rfl)) L hLx
    · exact hside V _ (subset_union_right.trans hUV.subset) x (hV.1 (Or.inl rfl)) L hLx
  · intro j; fin_cases j
    · exact hside U _ (subset_union_left.trans hUV.subset) y (hU.1 (Or.inr rfl)) R hRy
    · exact hside V _ (subset_union_right.trans hUV.subset) y (hV.1 (Or.inr rfl)) R hRy
  · intro j; fin_cases j
    · exact hside u _ (subset_union_left.trans huv.subset) a (hu.1 (Or.inl rfl)) L hLa
    · exact hside v _ (subset_union_right.trans huv.subset) a (hv.1 (Or.inl rfl)) L hLa
  · intro j; fin_cases j
    · exact hside u _ (subset_union_left.trans huv.subset) b (hu.1 (Or.inr rfl)) R hRb
    · exact hside v _ (subset_union_right.trans huv.subset) b (hv.1 (Or.inr rfl)) R hRb
  · intro j; fin_cases j
    · change IsFinitePLBallPair P2 (A \ interior S) ((U ∪ u) ∪ (L ∪ R))
      simpa only [← huA] using hAball
    · change IsFinitePLBallPair P2 (B \ interior S) ((V ∪ v) ∪ (L ∪ R))
      simpa only [← hvB] using hBball
  · change (A \ interior S) ∪ (B \ interior S) = T \ interior S
    rw [← union_sdiff_distrib, hAB]
  · change (A \ interior S) ∩ (B \ interior S) = L ∪ R
    have hsd : (A \ interior S) ∩ (B \ interior S) = (A ∩ B) \ interior S := by
      ext z
      simp only [mem_inter_iff, mem_sdiff]
      tauto
    rw [hsd, hAiB, hS.interior_eq_sdiff_of_finrank_eq rfl]
    ext z
    constructor
    · rintro ⟨(hzL | hzW) | hzR, hn⟩
      · exact Or.inl hzL
      · have hzsq : z ∈ frontier S := by
          by_contra hno
          exact hn ⟨hWS hzW, hno⟩
        rcases hWq.subset ⟨hzW, hzsq⟩ with rfl | rfl
        · exact Or.inl haL
        · exact Or.inr hbR
      · exact Or.inr hzR
    · intro hz
      refine ⟨hz.elim (fun h ↦ Or.inl (Or.inl h)) Or.inr, ?_⟩
      rintro ⟨hzS, hn⟩
      rcases hz with hz | hz
      · have he := hLS.subset ⟨hz, hzS⟩
        exact hn (he ▸ ha)
      · have he := hRS.subset ⟨hz, hzS⟩
        exact hn (he ▸ hb)

end PoincareConjecture.M76.Dehn
