import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.CornerArcStrip
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.FourArcRectangle

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

private theorem vertical_interval_ball {b d : ℝ} (hbd : b < d) :
    IsFinitePLBallPair ℝ ({0} ×ˢ Icc b d : Set (ℝ × ℝ)) {(0, b), (0, d)} := by
  let f : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ 0).prod (ContinuousAffineMap.id ℝ ℝ)
  have h := (isFinitePLBallPair_Icc hbd).affine_image f (by
    intro x _ y _ he
    exact congrArg Prod.snd he)
  have hi : f '' Icc b d = ({0} ×ˢ Icc b d : Set (ℝ × ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rfl, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.2, hy, Prod.ext hx.symm rfl⟩
  rw [hi, image_insert_eq, image_singleton] at h
  exact h

private theorem horizontal_interval_ball {a c : ℝ} (hac : a < c) :
    IsFinitePLBallPair ℝ (Icc a c ×ˢ {0} : Set (ℝ × ℝ)) {(a, 0), (c, 0)} := by
  let f : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ 0)
  have h := (isFinitePLBallPair_Icc hac).affine_image f (by
    intro x _ y _ he
    exact congrArg Prod.fst he)
  have hi : f '' Icc a c = (Icc a c ×ˢ {0} : Set (ℝ × ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.1, hx, Prod.ext rfl hy.symm⟩
  rw [hi, image_insert_eq, image_singleton] at h
  exact h

private theorem proper_arc_boundary_inter
    {W L : Set (ℝ × ℝ)} {p q : ℝ × ℝ}
    (hW : IsFinitePLBallPair ℝ W {p, q})
    (hproper : W \ {p, q} ⊆ base \ frontier base)
    (hL : L ⊆ frontier base) : W ∩ L = {p, q} ∩ L := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    by_contra hn
    exact (hproper ⟨hx.1, hn⟩).2 (hL hx.2)
  · exact inter_subset_inter_left _ hW.1

theorem exists_corner_arc_rectangle
    {a b c d : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    {W Z : Set (ℝ × ℝ)} (hW : IsFinitePLBallPair ℝ W {(0, b), (a, 0)})
    (hZ : IsFinitePLBallPair ℝ Z {(0, d), (c, 0)})
    (hproperW : W \ {(0, b), (a, 0)} ⊆ base \ frontier base)
    (hproperZ : Z \ {(0, d), (c, 0)} ⊆ base \ frontier base)
    (hdis : Disjoint W Z) (hac : a < c) :
    ∃ A M D V : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) A (rimArc a b ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) M (W ∪ (Z ∪ edgeIntervals a b c d)) ∧
      IsFinitePLBallPair (ℝ × ℝ) D (Z ∪ V) ∧
      (A ∪ M) ∪ D = base ∧ A ∩ M = W ∧ M ∩ D = Z ∧ Disjoint A D ∧
      A ∩ frontier base = rimArc a b ∧
      M ∩ frontier base = edgeIntervals a b c d ∧ D ∩ frontier base = V ∧
      ∃ C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M,
        C.IsFinitePL ∧
        (∀ x, (C x : ℝ × ℝ) ∈ W ↔ (x : ℝ × ℝ).2 = 0) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ Z ↔ (x : ℝ × ℝ).2 = 1) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ ({0} ×ˢ Icc b d) ↔ (x : ℝ × ℝ).1 = 0) ∧
        (∀ x, (C x : ℝ × ℝ) ∈ (Icc a c ×ˢ {0}) ↔ (x : ℝ × ℝ).1 = 1) := by
  have hbd := (endpoint_order_of_disjoint_arcs ha hb hc hd hW hZ
    hproperW hproperZ hdis).2.2.mp hac
  obtain ⟨A, M, D, V, hA, hM, hD, hcover, hAM, hMD, hAD, hAB, hMB, hDB⟩ :=
    exists_corner_arc_strip ha hb hc hd hW hZ hproperW hproperZ hdis hac
  refine ⟨A, M, D, V, hA, hM, hD, hcover, hAM, hMD, hAD, hAB, hMB, hDB, ?_⟩
  have hL : ({0} ×ˢ Icc b d : Set (ℝ × ℝ)) ⊆ frontier base := by
    rintro x ⟨hx, hy⟩
    apply rimArc_subset_frontier hc hd
    exact Or.inl ⟨hx, uIcc_of_le hd.1.le ▸ ⟨hb.1.le.trans hy.1, hy.2⟩⟩
  have hR : (Icc a c ×ˢ {0} : Set (ℝ × ℝ)) ⊆ frontier base := by
    rintro x ⟨hx, hy⟩
    apply rimArc_subset_frontier hc hd
    exact Or.inr ⟨uIcc_of_le hc.1.le ▸ ⟨ha.1.le.trans hx.1, hx.2⟩, hy⟩
  have hWL : W ∩ ({0} ×ˢ Icc b d) = {(0, b)} := by
    rw [proper_arc_boundary_inter hW hproperW hL]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact (ha.1.ne' h.1).elim
    · rintro rfl
      exact ⟨Or.inl rfl, rfl, le_rfl, hbd.le⟩
  have hWR : W ∩ (Icc a c ×ˢ {0}) = {(a, 0)} := by
    rw [proper_arc_boundary_inter hW hproperW hR]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact (hb.1.ne' h.2).elim
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, ⟨le_rfl, hac.le⟩, rfl⟩
  have hZL : Z ∩ ({0} ×ˢ Icc b d) = {(0, d)} := by
    rw [proper_arc_boundary_inter hZ hproperZ hL]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · exact (hc.1.ne' h.1).elim
    · rintro rfl
      exact ⟨Or.inl rfl, rfl, hbd.le, le_rfl⟩
  have hZR : Z ∩ (Icc a c ×ˢ {0}) = {(c, 0)} := by
    rw [proper_arc_boundary_inter hZ hproperZ hR]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_prod, mem_Icc]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact (hd.1.ne' h.2).elim
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, ⟨hac.le, le_rfl⟩, rfl⟩
  apply exists_four_arc_rectangle (by simpa only [edgeIntervals, union_assoc] using hM)
    hW hZ (vertical_interval_ball hbd) (horizontal_interval_ball hac)
    (fun he => ha.1.ne (congrArg Prod.fst he))
    (fun he => hc.1.ne (congrArg Prod.fst he))
    (fun he => hbd.ne (congrArg Prod.snd he))
    (fun he => hac.ne (congrArg Prod.fst he)) hdis _ hWL hWR hZL hZR
  apply disjoint_left.mpr
  intro x hxL hxR
  exact (not_le_of_gt ha.1) (hxL.1 ▸ hxR.1.1)

end PoincareConjecture.M76.TriangleCorner
