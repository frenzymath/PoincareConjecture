import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.CornerArcRectangle

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

private theorem subset_middle_of_meets
    {E : Type*} [TopologicalSpace E] {A M D W Z T J : Set E}
    (hA : IsClosed A) (hM : IsClosed M) (hD : IsClosed D)
    (hcover : (A ∪ M) ∪ D = T) (hAM : A ∩ M = W) (hMD : M ∩ D = Z)
    (hAD : Disjoint A D) (hJ : IsPreconnected J) (hJT : J ⊆ T)
    (hJW : Disjoint J W) (hJZ : Disjoint J Z) (hmeet : (J ∩ M).Nonempty) : J ⊆ M := by
  have hAMD : (A ∪ M) ∩ D = Z := by
    ext x
    constructor
    · rintro ⟨hxA | hxM, hxD⟩
      · exact False.elim (disjoint_left.mp hAD hxA hxD)
      · exact hMD.subset ⟨hxM, hxD⟩
    · intro hx
      exact ⟨Or.inr (hMD.symm.subset hx).1, (hMD.symm.subset hx).2⟩
  rcases Dehn.isPreconnected_subset_one_cut_piece hJ (hA.union hM) hD
      (hJT.trans hcover.symm.subset) hAMD hJZ with hleft | hright
  · rcases Dehn.isPreconnected_subset_one_cut_piece hJ hA hM hleft hAM hJW with ha | hm
    · obtain ⟨x, hxJ, hxM⟩ := hmeet
      exact False.elim (disjoint_left.mp hJW hxJ (hAM.subset ⟨ha hxJ, hxM⟩))
    · exact hm
  · obtain ⟨x, hxJ, hxM⟩ := hmeet
    exact False.elim (disjoint_left.mp hJZ hxJ (hMD.subset ⟨hxM, hright hxJ⟩))

private theorem marked_rectangle_isConnected
    {M W Z : Set (ℝ × ℝ)}
    (C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M)
    (hC : C.IsFinitePL)
    (hW : ∀ x, (C x : ℝ × ℝ) ∈ W ↔ (x : ℝ × ℝ).2 = 0)
    (hZ : ∀ x, (C x : ℝ × ℝ) ∈ Z ↔ (x : ℝ × ℝ).2 = 1) :
    IsConnected (M \ (W ∪ Z)) := by
  obtain ⟨f, hf, hfC⟩ := hC
  have hsub : (Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 : Set (ℝ × ℝ)) ⊆
      Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Subset.rfl Ioo_subset_Icc_self
  have himage : f '' (Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = M \ (W ∪ Z) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hfC ⟨x, hsub hx⟩]
      refine ⟨(C _).property, ?_⟩
      rintro (hw | hz)
      · exact hx.2.1.ne' ((hW _).mp hw)
      · exact hx.2.2.ne ((hZ _).mp hz)
    · rintro y ⟨hyM, hy⟩
      obtain ⟨x, hx⟩ := C.surjective ⟨y, hyM⟩
      have hxy : (C x : ℝ × ℝ) = y := congrArg Subtype.val hx
      rw [← hxy] at hy ⊢
      have hw : (x : ℝ × ℝ).2 ≠ 0 := fun he => hy (Or.inl ((hW x).mpr he))
      have hz : (x : ℝ × ℝ).2 ≠ 1 := fun he => hy (Or.inr ((hZ x).mpr he))
      exact ⟨x, ⟨x.property.1, lt_of_le_of_ne x.property.2.1 hw.symm,
        lt_of_le_of_ne x.property.2.2 hz⟩, (hfC x).symm⟩
  rw [← himage]
  exact ((isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num)).prod
    (isConnected_Ioo (show (0 : ℝ) < 1 by norm_num))).image f (hf.continuousOn.mono hsub)

theorem exists_component_rectangle_between_consecutive_corner_arcs
    {ι : Type*} (a b : ι → ℝ) (d : ι → Set (ℝ × ℝ))
    (ha : ∀ i, a i ∈ Ioo (0 : ℝ) 1) (hb : ∀ i, b i ∈ Ioo (0 : ℝ) 1)
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {(0, b i), (a i, 0)})
    (hproper : ∀ i, d i \ {(0, b i), (a i, 0)} ⊆ base \ frontier base)
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (i j : ι) (hij : a i < a j)
    (hadj : ∀ k, ¬ (a i < a k ∧ a k < a j)) :
    ∃ M : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) M (d i ∪ (d j ∪ edgeIntervals (a i) (b i) (a j) (b j))) ∧
      M ∩ frontier base = edgeIntervals (a i) (b i) (a j) (b j) ∧
      (∀ k, k ≠ i → k ≠ j → Disjoint (d k) M) ∧
      (∀ x ∈ M \ (d i ∪ d j),
        connectedComponentIn (base \ ⋃ k, d k) x = M \ (d i ∪ d j)) ∧
      ∃ C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M,
        C.IsFinitePL ∧
        (∀ x, (C x : ℝ × ℝ) ∈ d i ↔ (x : ℝ × ℝ).2 = 0) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ d j ↔ (x : ℝ × ℝ).2 = 1) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ ({0} ×ˢ Icc (b i) (b j)) ↔ (x : ℝ × ℝ).1 = 0) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ (Icc (a i) (a j) ×ˢ {0}) ↔ (x : ℝ × ℝ).1 = 1) := by
  classical
  have hine : i ≠ j := fun he => (he ▸ hij).false
  obtain ⟨A, M, D, V, hA, hM, hD, hcover, hAM, hMD, hAD, _, hMB, _, C, hC,
      hCW, hCZ, hCL, hCR⟩ := exists_corner_arc_rectangle (ha i) (hb i) (ha j) (hb j)
        (hd i) (hd j) (hproper i) (hproper j) (hdis hine) hij
  have hdsub (k : ι) : d k ⊆ base := by
    intro x hx
    by_cases he : x ∈ ({(0, b k), (a k, 0)} : Set (ℝ × ℝ))
    · exact isFinitePLBallPair_base.1 (rimArc_subset_frontier (ha k) (hb k)
        ((rimArc_ballPair (ha k).1 (hb k).1).1 he))
    · exact (hproper k ⟨hx, he⟩).1
  have hother (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : Disjoint (d k) M := by
    apply disjoint_left.mpr
    intro x hxk hxM
    have hkM := subset_middle_of_meets hA.isCompact.isClosed hM.isCompact.isClosed
      hD.isCompact.isClosed hcover hAM hMD hAD (hd k).isConnected.isPreconnected
      (hdsub k) (hdis hki) (hdis hkj) ⟨x, hxk, hxM⟩
    have hpoint : (a k, (0 : ℝ)) ∈ d k := (hd k).1 (by simp)
    have hpointB : (a k, (0 : ℝ)) ∈ frontier base :=
      rimArc_subset_frontier (ha k) (hb k) ((rimArc_ballPair (ha k).1 (hb k).1).1 (by simp))
    have hi : a i ≤ a k ∧ a k ≤ a j := by
      rcases hMB.subset ⟨hkM hpoint, hpointB⟩ with hleft | hright
      · exact False.elim ((ha k).1.ne' hleft.1)
      · exact hright.1
    have hai : a k ≠ a i := by
      intro he
      exact disjoint_left.mp (hdis hki) hpoint (he.symm ▸ (hd i).1 (by simp))
    have haj : a k ≠ a j := by
      intro he
      exact disjoint_left.mp (hdis hkj) hpoint (he.symm ▸ (hd j).1 (by simp))
    exact hadj k ⟨lt_of_le_of_ne hi.1 hai.symm, lt_of_le_of_ne hi.2 haj⟩
  have hMT : M ⊆ base := fun x hx => hcover.subset (Or.inl (Or.inr hx))
  have hregion : M \ (d i ∪ d j) ⊆ base \ ⋃ k, d k := by
    intro x hx
    refine ⟨hMT hx.1, ?_⟩
    rintro ⟨_, ⟨k, rfl⟩, hxk⟩
    by_cases hki : k = i
    · exact hx.2 (Or.inl (hki ▸ hxk))
    by_cases hkj : k = j
    · exact hx.2 (Or.inr (hkj ▸ hxk))
    exact disjoint_left.mp (hother k hki hkj) hxk hx.1
  have hconn := marked_rectangle_isConnected C hC hCW hCZ
  refine ⟨M, hM, hMB, hother, ?_, C, hC, hCW, hCZ, hCL, hCR⟩
  intro x hx
  apply Subset.antisymm
  · have hxcomp := mem_connectedComponentIn (hregion hx)
    have hcompM := subset_middle_of_meets hA.isCompact.isClosed hM.isCompact.isClosed
      hD.isCompact.isClosed hcover hAM hMD hAD isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (disjoint_left.mpr (fun y hy hyi => (connectedComponentIn_subset _ _ hy).2
        (mem_iUnion.mpr ⟨i, hyi⟩)))
      (disjoint_left.mpr (fun y hy hyj => (connectedComponentIn_subset _ _ hy).2
        (mem_iUnion.mpr ⟨j, hyj⟩))) ⟨x, hxcomp, hx.1⟩
    intro y hy
    refine ⟨hcompM hy, ?_⟩
    rintro (hyi | hyj)
    · exact (connectedComponentIn_subset _ _ hy).2 (mem_iUnion.mpr ⟨i, hyi⟩)
    · exact (connectedComponentIn_subset _ _ hy).2 (mem_iUnion.mpr ⟨j, hyj⟩)
  · exact hconn.isPreconnected.subset_connectedComponentIn hx hregion

theorem exists_component_rectangle_of_boundary_adjacency
    {ι : Type*} (d r : ι → Set (ℝ × ℝ))
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ base) (hrim : ∀ i, r i = d i ∩ frontier base)
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (i j : ι) (hne : i ≠ j)
    {a b c e : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (he : e ∈ Ioo (0 : ℝ) 1)
    (hi : r i = {(0, b), (a, 0)}) (hj : r j = {(0, e), (c, 0)})
    (hac : a < c)
    (hadj : ∀ k, k ≠ i → k ≠ j → ¬ r k ⊆ edgeIntervals a b c e) :
    ∃ M : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) M (d i ∪ (d j ∪ edgeIntervals a b c e)) ∧
      M ∩ frontier base = edgeIntervals a b c e ∧
      (∀ k, k ≠ i → k ≠ j → Disjoint (d k) M) ∧
      (∀ x ∈ M \ (d i ∪ d j),
        connectedComponentIn (base \ ⋃ k, d k) x = M \ (d i ∪ d j)) ∧
      ∃ C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M,
        C.IsFinitePL ∧
        (∀ x, (C x : ℝ × ℝ) ∈ d i ↔ (x : ℝ × ℝ).2 = 0) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ d j ↔ (x : ℝ × ℝ).2 = 1) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ ({0} ×ˢ Icc b e) ↔ (x : ℝ × ℝ).1 = 0) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ (Icc a c ×ˢ {0}) ↔ (x : ℝ × ℝ).1 = 1) := by
  have hproper (k : ι) : d k \ r k ⊆ base \ frontier base := by
    intro x hx
    exact ⟨hsub k hx.1, fun hf => hx.2 ((hrim k).symm.subset ⟨hx.1, hf⟩)⟩
  obtain ⟨A, M, D, V, hA, hM, hD, hcover, hAM, hMD, hAD, _, hMB, _, C, hC,
      hCW, hCZ, hCL, hCR⟩ := exists_corner_arc_rectangle ha hb hc he
        (hi ▸ hd i) (hj ▸ hd j) (hi ▸ hproper i) (hj ▸ hproper j) (hdis hne) hac
  have hother (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : Disjoint (d k) M := by
    apply disjoint_left.mpr
    intro x hxk hxM
    have hkM := subset_middle_of_meets hA.isCompact.isClosed hM.isCompact.isClosed
      hD.isCompact.isClosed hcover hAM hMD hAD (hd k).isConnected.isPreconnected
      (hsub k) (hdis hki) (hdis hkj) ⟨x, hxk, hxM⟩
    apply hadj k hki hkj
    intro y hy
    have hy' := (hrim k).subset hy
    exact hMB.subset ⟨hkM hy'.1, hy'.2⟩
  have hMT : M ⊆ base := fun x hx => hcover.subset (Or.inl (Or.inr hx))
  have hregion : M \ (d i ∪ d j) ⊆ base \ ⋃ k, d k := by
    classical
    intro x hx
    refine ⟨hMT hx.1, ?_⟩
    rintro ⟨_, ⟨k, rfl⟩, hxk⟩
    by_cases hki : k = i
    · exact hx.2 (Or.inl (hki ▸ hxk))
    by_cases hkj : k = j
    · exact hx.2 (Or.inr (hkj ▸ hxk))
    exact disjoint_left.mp (hother k hki hkj) hxk hx.1
  have hconn := marked_rectangle_isConnected C hC hCW hCZ
  refine ⟨M, hM, hMB, hother, ?_, C, hC, hCW, hCZ, hCL, hCR⟩
  intro x hx
  apply Subset.antisymm
  · have hxcomp := mem_connectedComponentIn (hregion hx)
    have hcompM := subset_middle_of_meets hA.isCompact.isClosed hM.isCompact.isClosed
      hD.isCompact.isClosed hcover hAM hMD hAD isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (disjoint_left.mpr (fun y hy hyi => (connectedComponentIn_subset _ _ hy).2
        (mem_iUnion.mpr ⟨i, hyi⟩)))
      (disjoint_left.mpr (fun y hy hyj => (connectedComponentIn_subset _ _ hy).2
        (mem_iUnion.mpr ⟨j, hyj⟩))) ⟨x, hxcomp, hx.1⟩
    intro y hy
    refine ⟨hcompM hy, ?_⟩
    rintro (hyi | hyj)
    · exact (connectedComponentIn_subset _ _ hy).2 (mem_iUnion.mpr ⟨i, hyi⟩)
    · exact (connectedComponentIn_subset _ _ hy).2 (mem_iUnion.mpr ⟨j, hyj⟩)
  · exact hconn.isPreconnected.subset_connectedComponentIn hx hregion

end PoincareConjecture.M76.TriangleCorner
