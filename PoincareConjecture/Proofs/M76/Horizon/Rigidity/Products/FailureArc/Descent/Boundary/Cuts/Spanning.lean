import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Cuts.SpanningParts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

private theorem join_spanning_interval_pairs
    {U V : Set P2} {a b c : P2} (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {b, c}) (hab : a ≠ b) (hbc : b ≠ c)
    (hUV : U ∩ V = {b}) : IsFinitePLBallPair ℝ (U ∪ V) {a, c} := by
  obtain ⟨p, hp, hp0, hp1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨q, hq, hq0, hq1⟩ := hV.exists_unitInterval_chart_with_endpoints hbc
  exact isFinitePLBallPair_joined_intervals p q hp hq hp0 hp1 hq0 hq1 hUV

theorem exists_shell_dissection_with_spanning_sides
    {S T L R : Set P2} {a b x y : P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (hL : IsFinitePLBallPair ℝ L {x, a})
    (hR : IsFinitePLBallPair ℝ R {b, y})
    (ha : a ∈ frontier S) (hb : b ∈ frontier S)
    (hx : x ∈ frontier T) (hy : y ∈ frontier T)
    (hLS : L ∩ S = {a}) (hRS : R ∩ S = {b})
    (hLp : L \ {x} ⊆ interior T) (hRp : R \ {y} ⊆ interior T)
    (hLR : Disjoint L R) :
    ∃ D : NestedShellDissection S T,
      D.x = x ∧ D.y = y ∧ D.a = a ∧ D.b = b ∧ D.left = L ∧ D.right = R := by
  have haS := hS.1 ha
  have hbS := hS.1 hb
  have hxS : x ∉ S := fun h ↦ hx.2 (hST h)
  have hyS : y ∉ S := fun h ↦ hy.2 (hST h)
  have hxL : x ∈ L := hL.1 (Or.inl rfl)
  have haL : a ∈ L := hL.1 (Or.inr rfl)
  have hbR : b ∈ R := hR.1 (Or.inl rfl)
  have hyR : y ∈ R := hR.1 (Or.inr rfl)
  have hab : a ≠ b := fun h ↦ disjoint_left.mp hLR haL (h ▸ hbR)
  have hxy : x ≠ y := fun h ↦ disjoint_left.mp hLR hxL (h ▸ hyR)
  have hxa : x ≠ a := fun h ↦ hxS (h ▸ haS)
  have hby : b ≠ y := fun h ↦ hyS (h ▸ hbS)
  obtain ⟨W, hW, hWS, hWq, hWp⟩ :=
    exists_proper_interval_between_boundary_points hS ha hb hab
  have hLW : L ∩ W = {a} := by
    apply Subset.antisymm ((inter_subset_inter_right _ hWS).trans hLS.subset)
    rintro z rfl
    exact ⟨haL, hW.1 (Or.inl rfl)⟩
  have hLWR : (L ∪ W) ∩ R = {b} := by
    apply Subset.antisymm
    · rintro z ⟨hz | hz, hzR⟩
      · exact (disjoint_left.mp hLR hz hzR).elim
      · exact hRS.subset ⟨hzR, hWS hz⟩
    · rintro z rfl
      exact ⟨Or.inr (hW.1 (Or.inr rfl)), hbR⟩
  have hxb : x ≠ b := fun h ↦ disjoint_left.mp hLR hxL (h ▸ hbR)
  have hZ := join_spanning_interval_pairs
    (join_spanning_interval_pairs hL hW hxa hab hLW) hR hxb hby hLWR
  have hZS : ((L ∪ W) ∪ R) ∩ S = W := by
    ext z
    constructor
    · rintro ⟨(hz | hz) | hz, hzS⟩
      · exact (hLS.subset ⟨hz, hzS⟩) ▸ hW.1 (Or.inl rfl)
      · exact hz
      · exact (hRS.subset ⟨hz, hzS⟩) ▸ hW.1 (Or.inr rfl)
    · exact fun hz ↦ ⟨Or.inl (Or.inr hz), hWS hz⟩
  have hZp : ((L ∪ W) ∪ R) \ {x, y} ⊆ T \ frontier T := by
    rw [← hT.interior_eq_sdiff_of_finrank_eq rfl]
    intro z hz
    rcases hz.1 with (hzL | hzW) | hzR
    · exact hLp ⟨hzL, fun h ↦ hz.2 (Or.inl h)⟩
    · exact hST (hWS hzW)
    · exact hRp ⟨hzR, fun h ↦ hz.2 (Or.inr h)⟩
  have hST' : S ⊆ T \ frontier T := by
    simpa only [hT.interior_eq_sdiff_of_finrank_eq rfl] using hST
  obtain ⟨A, B, U, V, u, v, hA, hB, hAB, hAiB, hAU, hBV,
    hU, hV, hUV, hUiV, hu, hv, huv, huiv, huA, hvB, hSA, hSB, hup, hvp⟩ :=
    exists_nested_disk_cut_halves hS hT hST' hW hZ hab hxy ha hb hx hy hWp hZp hWS hZS
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
      by_contra hn
      exact hz.2.2 (hLp ⟨hz.1, hn⟩)
    · rintro z rfl
      exact ⟨hxL, hx⟩
  have hRy : R ∩ frontier T = {y} := by
    apply Subset.antisymm
    · intro z hz
      by_contra hn
      exact hz.2.2 (hRp ⟨hz.1, hn⟩)
    · rintro z rfl
      exact ⟨hyR, hy⟩
  have hUS : Disjoint U S := disjoint_left.mpr fun z hz hs ↦
    (hST' hs).2 (hUV.subset (Or.inl hz))
  have hVS : Disjoint V S := disjoint_left.mpr fun z hz hs ↦
    (hST' hs).2 (hUV.subset (Or.inr hz))
  have hAball := shell_half_complement_of_spanning_sides hS hA (huA ▸ hSA) hW
    (huA ▸ hu) hab (huA ▸ hup) hUS hLS hRS hWS haL hbR
  have hB' : IsFinitePLBallPair P2 B (V ∪ ((L ∪ W) ∪ R)) := by
    simpa only [union_comm] using hB
  have hvp' : (frontier S ∩ B) \ {a, b} ⊆ B \ (V ∪ ((L ∪ W) ∪ R)) := by
    simpa only [hvB, union_comm] using hvp
  have hBball := shell_half_complement_of_spanning_sides hS hB' (hvB ▸ hSB) hW
    (hvB ▸ hv) hab hvp' hVS hLS hRS hWS haL hbR
  have hside (q r : Set P2) (hq : q ⊆ r) (p : P2) (hp : p ∈ q)
      (C : Set P2) (hC : C ∩ r = {p}) : q ∩ C = {p} := by
    apply Subset.antisymm
    · exact fun z hz ↦ hC.subset ⟨hz.2, hq hz.1⟩
    · rintro z rfl
      exact ⟨hp, (hC.symm.subset rfl).1⟩
  let D : NestedShellDissection S T := {
    x := x, y := y, a := a, b := b
    outer := ![U, V], inner := ![u, v], left := L, right := R
    disk := ![A \ interior S, B \ interior S]
    outer_ball := by intro j; fin_cases j <;> assumption
    inner_ball := by intro j; fin_cases j <;> assumption
    left_ball := hL
    right_ball := by simpa only [pair_comm] using hR
    xy_ne := hxy, ab_ne := hab, xa_ne := hxa, yb_ne := hby.symm
    outer_cover := hUV, inner_cover := huv, outer_inter := hUiV, inner_inter := huiv
    cross_disjoint := by
      intro j; fin_cases j
      · exact hUS.mono_right (fun z hz ↦ hS.1 (huv.subset (Or.inl hz)))
      · exact hVS.mono_right (fun z hz ↦ hS.1 (huv.subset (Or.inr hz)))
    sides_disjoint := hLR
    outer_left := by
      intro j; fin_cases j
      · exact hside U _ (subset_union_left.trans hUV.subset) x (hU.1 (Or.inl rfl)) L hLx
      · exact hside V _ (subset_union_right.trans hUV.subset) x (hV.1 (Or.inl rfl)) L hLx
    outer_right := by
      intro j; fin_cases j
      · exact hside U _ (subset_union_left.trans hUV.subset) y (hU.1 (Or.inr rfl)) R hRy
      · exact hside V _ (subset_union_right.trans hUV.subset) y (hV.1 (Or.inr rfl)) R hRy
    inner_left := by
      intro j; fin_cases j
      · exact hside u _ (subset_union_left.trans huv.subset) a (hu.1 (Or.inl rfl)) L hLa
      · exact hside v _ (subset_union_right.trans huv.subset) a (hv.1 (Or.inl rfl)) L hLa
    inner_right := by
      intro j; fin_cases j
      · exact hside u _ (subset_union_left.trans huv.subset) b (hu.1 (Or.inr rfl)) R hRb
      · exact hside v _ (subset_union_right.trans huv.subset) b (hv.1 (Or.inr rfl)) R hRb
    disk_ball := by
      intro j; fin_cases j
      · change IsFinitePLBallPair P2 (A \ interior S) ((U ∪ u) ∪ (L ∪ R))
        simpa only [← huA] using hAball
      · change IsFinitePLBallPair P2 (B \ interior S) ((V ∪ v) ∪ (L ∪ R))
        simpa only [← hvB] using hBball
    disk_cover := by
      change (A \ interior S) ∪ (B \ interior S) = T \ interior S
      rw [← union_sdiff_distrib, hAB]
    disk_inter := by
      change (A \ interior S) ∩ (B \ interior S) = L ∪ R
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
        · exact hn ((hLS.subset ⟨hz, hzS⟩) ▸ ha)
        · exact hn ((hRS.subset ⟨hz, hzS⟩) ▸ hb) }
  exact ⟨D, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.M76.Dehn
