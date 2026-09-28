import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ProperArcPairNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.BoundaryArcCompression
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.PlanarPLDiskUniqueness
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)

private theorem exists_exterior_disk_caps
    {D q B w W : Set V} {a b : V}
    (hD : IsFinitePLBallPair V D q) (hB : IsFinitePLBallPair V B (w ∪ W))
    (hw : IsFinitePLBallPair ℝ w {a, b}) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ q) (hb : b ∈ q)
    (hproper : w \ {a, b} ⊆ D \ q) (hProper : W \ {a, b} ⊆ D \ q)
    (hmeet : w ∩ W = {a, b}) :
    ∃ C₀ C₁ q₀ q₁ : Set V,
      IsFinitePLBallPair V C₀ q₀ ∧ IsFinitePLBallPair V C₁ q₁ ∧
      C₀ ∩ B = w ∧ C₁ ∩ B = W ∧ C₀ ∩ C₁ ⊆ {a, b} ∧
      (C₀ ∪ B) ∪ C₁ = D ∧ w ⊆ q₀ ∧ W ⊆ q₁ := by
  obtain ⟨u, v, hu, hv, huv, huvi⟩ := hD.exists_boundary_arcs ha hb hab
  obtain ⟨L₀, L₁, hL₀, hL₁, hcover, hcommon, houter₀, houter₁⟩ :=
    hD.exists_proper_arc_cut hu hv hW hab huvi.subset huv hProper
  have huq : u ⊆ q := subset_union_left.trans huv.subset
  have hvq : v ⊆ q := subset_union_right.trans huv.subset
  obtain ⟨x, hx⟩ := hw.sdiff_nonempty
  have hnot (y : V) (hy : y ∈ w \ {a, b}) : y ∉ W :=
    fun hyW => hy.2 (hmeet.subset ⟨hy.1, hyW⟩)
  have hinside {L l : Set V} (hL : IsFinitePLBallPair V L (l ∪ W))
      (hlq : l ⊆ q) (hxL : x ∈ L) : w \ {a, b} ⊆ L \ (l ∪ W) := by
    have havoid (y : V) (hy : y ∈ w \ {a, b}) : y ∉ l ∪ W := by
      rintro (hyl | hyW)
      · exact (hproper hy).2 (hlq hyl)
      · exact hnot y hy hyW
    have hdis : Disjoint (frontier (interior L)) (w \ {a, b}) := by
      rw [hL.frontier_interior_of_finrank_eq rfl]
      exact disjoint_left.mpr (fun y hy hz => havoid y hz hy)
    have hxint : x ∈ interior L :=
      (hL.interior_eq_sdiff_of_finrank_eq rfl).symm.subset ⟨hxL, havoid x hx⟩
    have hh := hw.isConnected_sdiff.isPreconnected.m76_subset_of_disjoint_frontier
      isOpen_interior hdis ⟨x, hx, hxint⟩
    exact hh.trans (hL.interior_eq_sdiff_of_finrank_eq rfl).subset
  obtain ⟨L, C, l, r, hL, hC, hl, hr, hlW, hLC, hLCW, hwL⟩ :
      ∃ L C l r : Set V,
        IsFinitePLBallPair V L (l ∪ W) ∧ IsFinitePLBallPair V C (W ∪ r) ∧
        IsFinitePLBallPair ℝ l {a, b} ∧ IsFinitePLBallPair ℝ r {a, b} ∧
        l ∩ W = {a, b} ∧ L ∪ C = D ∧ L ∩ C = W ∧
        w \ {a, b} ⊆ L \ (l ∪ W) := by
    rcases hcover.symm.subset (hproper hx).1 with hxL | hxL
    · refine ⟨L₀, L₁, u, v, hL₀, hL₁, hu, hv, ?_, hcover, hcommon,
        hinside hL₀ huq hxL⟩
      apply Subset.antisymm
      · rintro y ⟨hyu, hyW⟩
        by_contra hn
        exact (hProper ⟨hyW, hn⟩).2 (huq hyu)
      · exact subset_inter hu.1 hW.1
    · have hL₁' : IsFinitePLBallPair V L₁ (v ∪ W) := by simpa only [union_comm] using hL₁
      have hL₀' : IsFinitePLBallPair V L₀ (W ∪ u) := by simpa only [union_comm] using hL₀
      refine ⟨L₁, L₀, v, u, hL₁', hL₀', hv, hu, ?_,
        (union_comm _ _).trans hcover, (inter_comm _ _).trans hcommon,
        hinside hL₁' hvq hxL⟩
      apply Subset.antisymm
      · rintro y ⟨hyv, hyW⟩
        by_contra hn
        exact (hProper ⟨hyW, hn⟩).2 (hvq hyv)
      · exact subset_inter hv.1 hW.1
  obtain ⟨E, B', hE, hB', hEB, hEBw, hEl, hB'W⟩ :=
    hL.exists_proper_arc_cut hl hW hw hab hlW.subset rfl hwL
  have hBB : B' = B := by
    apply hB'.eq_of_same_planar_rim
    simpa only [union_comm] using hB
  subst B'
  have hBL : B ⊆ L := subset_union_right.trans hEB.subset
  have hEL : E ⊆ L := subset_union_left.trans hEB.subset
  have hCB : C ∩ B = W := by
    apply Subset.antisymm
    · exact fun y hy => hLCW.subset ⟨hBL hy.2, hy.1⟩
    · exact fun y hy => ⟨(hLCW.symm.subset hy).2, hB.1 (Or.inr hy)⟩
  have hEC : E ∩ C ⊆ {a, b} := by
    intro y hy
    have hyW : y ∈ W := hLCW.subset ⟨hEL hy.1, hy.2⟩
    have hyl : y ∈ l := hEl.subset ⟨hy.1, Or.inr hyW⟩
    exact hlW.subset ⟨hyl, hyW⟩
  refine ⟨E, C, l ∪ w, W ∪ r, hE, hC, hEBw, hCB, hEC, ?_,
    subset_union_right, subset_union_left⟩
  rw [hEB, hLC]

private theorem exists_union_compression
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} {f g : E → E}
    (hf : FinitePiecewiseAffineOn f A) (hg : FinitePiecewiseAffineOn g B)
    (hfi : InjOn f A) (hgi : InjOn g B) (hfA : MapsTo f A A) (hgB : MapsTo g B B)
    (hfixf : EqOn f id (A ∩ B)) (hfixg : EqOn g id (A ∩ B)) :
    ∃ F : E → E, FinitePiecewiseAffineOn F (A ∪ B) ∧ InjOn F (A ∪ B) ∧
      MapsTo F (A ∪ B) (A ∪ B) ∧ EqOn F f A ∧ EqOn F g B := by
  classical
  let F := A.piecewise f g
  have hFa : EqOn F f A := fun x hx => piecewise_eq_of_mem A f g hx
  have hFb : EqOn F g B := by
    intro x hx
    by_cases hxA : x ∈ A
    · rw [hFa hxA, hfixf ⟨hxA, hx⟩, hfixg ⟨hxA, hx⟩]
    · exact piecewise_eq_of_notMem A f g hxA
  have hcross {x y : E} (hx : x ∈ A) (hy : y ∈ B) (heq : f x = g y) : x = y := by
    have hzA : g y ∈ A := heq ▸ hfA hx
    have hzB : g y ∈ B := hgB hy
    have hxz : x = g y := hfi hx hzA (heq.trans (hfixf ⟨hzA, hzB⟩).symm)
    have hyz : y = g y := hgi hy hzB (hfixg ⟨hzA, hzB⟩).symm
    exact hxz.trans hyz.symm
  refine ⟨F, finitePiecewiseAffineOn_union (hf.congr hFa.symm) (hg.congr hFb.symm),
    ?_, ?_, hFa, hFb⟩
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · apply hfi hx hy
      rwa [hFa hx, hFa hy] at hxy
    · apply hcross hx hy
      rwa [hFa hx, hFb hy] at hxy
    · apply (hcross hy hx _).symm
      simpa only [hFa hy, hFb hx] using hxy.symm
    · apply hgi hx hy
      rwa [hFb hx, hFb hy] at hxy
  · intro x hx
    rcases hx with hx | hx
    · rw [hFa hx]
      exact Or.inl (hfA hx)
    · rw [hFb hx]
      exact Or.inr (hgB hx)

theorem exists_proper_arc_pair_compression
    {D q B w W U : Set V} {a b : V}
    (hD : IsFinitePLBallPair V D q) (hB : IsFinitePLBallPair V B (w ∪ W))
    (hw : IsFinitePLBallPair ℝ w {a, b}) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ q) (hb : b ∈ q)
    (hproper : w \ {a, b} ⊆ D \ q) (hProper : W \ {a, b} ⊆ D \ q)
    (hmeet : w ∩ W = {a, b}) (hU : IsOpen U) (hBU : B ⊆ U) :
    ∃ F : V → V, FinitePiecewiseAffineOn F D ∧ InjOn F D ∧
      MapsTo F D (D ∩ U) ∧ EqOn F id B ∧ B ⊆ D := by
  obtain ⟨C₀, C₁, q₀, q₁, hC₀, hC₁, hC₀B, hC₁B, hC₀C₁, hcover, hwq, hWq⟩ :=
    exists_exterior_disk_caps hD hB hw hW hab ha hb hproper hProper hmeet
  have hwB : w ⊆ B := subset_union_left.trans hB.1
  have hWB : W ⊆ B := subset_union_right.trans hB.1
  obtain ⟨f, hf, hfi, hfmap, hffix⟩ :=
    exists_disk_compression_toward_boundary_arc hC₀ hw hab hwq hU (hwB.trans hBU)
  obtain ⟨g, hg, hgi, hgmap, hgfix⟩ :=
    exists_disk_compression_toward_boundary_arc hC₁ hW hab hWq hU (hWB.trans hBU)
  have hid : FinitePiecewiseAffineOn (id : V → V) B := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKB, _⟩, _⟩, _⟩ := hB
    exact ⟨K, hK, hKB, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V)⟩
  obtain ⟨F₀, hF₀, hF₀i, hF₀map, hF₀f, hF₀id⟩ :=
    exists_union_compression hf hid hfi (fun _ _ _ _ h => h)
      (fun x hx => (hfmap hx).1) (fun _ hx => hx)
      (hC₀B.symm ▸ hffix) (fun _ _ => rfl)
  have hiW : (C₀ ∪ B) ∩ C₁ ⊆ W := by
    rintro x ⟨hx | hx, hxC⟩
    · exact hW.1 (hC₀C₁ ⟨hx, hxC⟩)
    · exact hC₁B.subset ⟨hxC, hx⟩
  have hifix : EqOn F₀ id ((C₀ ∪ B) ∩ C₁) := by
    intro x hx
    exact hF₀id (hWB (hiW hx))
  obtain ⟨F, hF, hFi, hFmap, hFF₀, hFg⟩ :=
    exists_union_compression hF₀ hg hF₀i hgi hF₀map
      (fun x hx => (hgmap hx).1) hifix (hgfix.mono hiW)
  have hFU : MapsTo F ((C₀ ∪ B) ∪ C₁) U := by
    rintro x ((hx | hx) | hx)
    · rw [hFF₀ (Or.inl hx), hF₀f hx]
      exact (hfmap hx).2
    · rw [hFF₀ (Or.inr hx), hF₀id hx]
      exact hBU hx
    · rw [hFg hx]
      exact (hgmap hx).2
  refine ⟨F, hcover ▸ hF, hcover ▸ hFi, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := hcover.symm.subset hx
    exact ⟨hcover.subset (hFmap hx'), hFU hx'⟩
  · intro x hx
    exact (hFF₀ (Or.inr hx)).trans (hF₀id hx)
  · exact subset_union_right.trans (subset_union_left.trans hcover.subset)

theorem exists_confined_proper_arc_pair_disk
    {W B U : Set V} {a b : V}
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a.1 < b.1)
    (ha : a.2 = 0) (hb : b.2 = 0)
    (hup : ∀ x ∈ W, 0 ≤ x.2)
    (haxis : W ∩ {x : V | x.2 = 0} = {a, b})
    (hB : IsFinitePLBallPair V B (segment ℝ a b ∪ W))
    (hU : IsOpen U) (hBU : B ⊆ U) :
    ∃ D : Set V, IsCompact D ∧ IsFinitePLBallPair V D (frontier D) ∧
      D ⊆ U ∧ B ⊆ D ∧ a ∈ frontier D ∧ b ∈ frontier D ∧
      W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      D ∩ {x : V | x.2 = 0} = segment ℝ a b := by
  have hab' : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  have hw : IsFinitePLBallPair ℝ (segment ℝ a b) {a, b} := by
    have hh := isFinitePLBallPair_affine_interval zero_lt_one
      (ContinuousAffineMap.lineMap a b) (AffineMap.lineMap_injective ℝ hab').injOn
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using hh
  obtain ⟨D₀, hcompact, hconvex, hD₀, ha₀, hb₀, hWD₀, hwD₀, hWint, hwint, hD₀axis⟩ :=
    exists_convex_proper_arc_pair_disk hW hab ha hb hup haxis
  have hmeet : segment ℝ a b ∩ W = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxW⟩
      have hx0 := (PlanarSegment.mem_segment_iff hab.ne).mp hx
      have hxz : x.2 = 0 := by
        simpa [PlanarSegment.height, ha, hb] using hx0.2
      exact haxis.subset ⟨hxW, hxz⟩
    · exact subset_inter hw.1 hW.1
  have hwproper : segment ℝ a b \ {a, b} ⊆ D₀ \ frontier D₀ :=
    hwint.trans (hD₀.interior_eq_sdiff_of_finrank_eq rfl).subset
  have hWproper : W \ {a, b} ⊆ D₀ \ frontier D₀ :=
    hWint.trans (hD₀.interior_eq_sdiff_of_finrank_eq rfl).subset
  obtain ⟨F, hF, hFi, hFmap, hFfix, hBD₀⟩ := exists_proper_arc_pair_compression
    hD₀ hB hw hW hab' ha₀ hb₀ hwproper hWproper hmeet hU hBU
  have himage := hD₀.image hF hFi
  have hfront := himage.frontier_eq_of_finrank_eq rfl
  have hBD : B ⊆ F '' D₀ := by
    intro x hx
    exact ⟨x, hBD₀ hx, hFfix hx⟩
  have hWB : W ⊆ B := subset_union_right.trans hB.1
  have hwB : segment ℝ a b ⊆ B := subset_union_left.trans hB.1
  have haB : a ∈ B := hwB (left_mem_segment ℝ a b)
  have hbB : b ∈ B := hwB (right_mem_segment ℝ a b)
  have hDsub : F '' D₀ ⊆ D₀ ∩ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hFmap hy
  refine ⟨F '' D₀, himage.isCompact, hfront.symm ▸ himage,
    hDsub.trans inter_subset_right, hBD, ?_, ?_, hWB.trans hBD, hwB.trans hBD,
    ?_, ?_, ?_⟩
  · rw [hfront]
    exact ⟨a, ha₀, hFfix haB⟩
  · rw [hfront]
    exact ⟨b, hb₀, hFfix hbB⟩
  · intro x hx
    have hh := hF.mem_interior_image rfl hFi (hWint hx)
    rwa [hFfix (hWB hx.1)] at hh
  · intro x hx
    have hh := hF.mem_interior_image rfl hFi (hwint hx)
    rwa [hFfix (hwB hx.1)] at hh
  · apply Subset.antisymm
    · exact fun x hx => hD₀axis.subset ⟨(hDsub hx.1).1, hx.2⟩
    · intro x hx
      exact ⟨hBD (hwB hx), (hD₀axis.symm.subset hx).2⟩

end PoincareConjecture.M76
