import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.CornerArcComponents
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem pair_subset_edgeIntervals
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 1) (hd : d ≤ 1)
    {p q : ℝ × ℝ} (hsub : ({p, q} : Set (ℝ × ℝ)) ⊆ edgeIntervals a b c d)
    (hleft : ¬ ({p, q} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ¬ ({p, q} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0}) :
    ∃ x ∈ Icc a c, ∃ y ∈ Icc b d, ({p, q} : Set (ℝ × ℝ)) = {(0, y), (x, 0)} := by
  have hp := hsub (show p ∈ ({p, q} : Set (ℝ × ℝ)) by simp)
  have hq := hsub (show q ∈ ({p, q} : Set (ℝ × ℝ)) by simp)
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · apply False.elim
    apply hleft
    rintro x (rfl | rfl)
    · exact ⟨hp.1, hb.trans hp.2.1, hp.2.2.trans hd⟩
    · exact ⟨hq.1, hb.trans hq.2.1, hq.2.2.trans hd⟩
  · refine ⟨q.1, hq.1, p.2, hp.2, ?_⟩
    have heP : p = (0, p.2) := Prod.ext hp.1 rfl
    have heQ : q = (q.1, 0) := Prod.ext rfl hq.2
    exact congrArg₂ (fun x y => ({x, y} : Set (ℝ × ℝ))) heP heQ
  · refine ⟨p.1, hp.1, q.2, hq.2, ?_⟩
    have heP : p = (p.1, 0) := Prod.ext rfl hp.2
    have heQ : q = (0, q.2) := Prod.ext hq.1 rfl
    rw [congrArg₂ (fun x y => ({x, y} : Set (ℝ × ℝ))) heP heQ, pair_comm]
  · apply False.elim
    apply hbottom
    rintro x (rfl | rfl)
    · exact ⟨⟨ha.trans hp.1.1, hp.1.2.trans hc⟩, hp.2⟩
    · exact ⟨⟨ha.trans hq.1.1, hq.1.2.trans hc⟩, hq.2⟩

theorem boundary_adjacency_of_no_intermediate_pair
    {ι : Type*} (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hends : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) ⊆ D k)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hleft : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (i j : ι) {a b c d : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hi : ({p i, q i} : Set (ℝ × ℝ)) = {(0, b), (a, 0)})
    (hj : ({p j, q j} : Set (ℝ × ℝ)) = {(0, d), (c, 0)})
    (hadj : ∀ k, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      ({p k, q k} : Set (ℝ × ℝ)) = {(0, y), (x, 0)} →
      ¬ (a < x ∧ x < c)) :
    ∀ k, k ≠ i → k ≠ j → ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ edgeIntervals a b c d := by
  intro k hki hkj hsub
  obtain ⟨x, hx, y, hy, heq⟩ := pair_subset_edgeIntervals ha.1.le hb.1.le hc.2.le hd.2.le
    hsub (hleft k) (hbottom k)
  have hpoint : (x, (0 : ℝ)) ∈ D k := hends k (heq.symm.subset (by simp))
  have hxa : x ≠ a := by
    intro he
    exact disjoint_left.mp (hdis hki) hpoint (he.symm ▸ hends i (hi.symm.subset (by simp)))
  have hxc : x ≠ c := by
    intro he
    exact disjoint_left.mp (hdis hkj) hpoint (he.symm ▸ hends j (hj.symm.subset (by simp)))
  exact hadj k x ⟨ha.1.trans_le hx.1, hx.2.trans_lt hc.2⟩
    y ⟨hb.1.trans_le hy.1, hy.2.trans_lt hd.2⟩ heq
    ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxc⟩

noncomputable def horizontalEndpoint (p q : ℝ × ℝ) : ℝ :=
  if p.2 = 0 then p.1 else q.1

theorem horizontalEndpoint_eq {p q : ℝ × ℝ} {x y : ℝ} (hy : y ≠ 0)
    (hpair : ({p, q} : Set (ℝ × ℝ)) = {(0, y), (x, 0)}) :
    horizontalEndpoint p q = x := by
  have hp : p ∈ ({(0, y), (x, 0)} : Set (ℝ × ℝ)) := hpair.subset (by simp)
  rcases hp with hp | hp
  · have hpe : p = (0, y) := hp
    have hq : q = (x, 0) := by
      have hm := hpair.symm.subset (show (x, (0 : ℝ)) ∈ ({(0, y), (x, 0)} : Set (ℝ × ℝ)) by simp)
      rcases hm with he | he
      · exact False.elim (hy (congrArg Prod.snd (hpe.symm.trans he.symm)))
      · exact (mem_singleton_iff.mp he).symm
    simp only [horizontalEndpoint, hpe, hy, if_false, hq]
  · have hpe : p = (x, 0) := mem_singleton_iff.mp hp
    simp only [horizontalEndpoint, hpe, if_true]

theorem exists_next_corner_pair
    {ι : Type*} [Finite ι] (p q : ι → ℝ × ℝ) (a : ℝ)
    (hnext : ∃ k, ∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1,
      ({p k, q k} : Set (ℝ × ℝ)) = {(0, y), (x, 0)} ∧ a < x) :
    ∃ j, ∃ c ∈ Ioo (0 : ℝ) 1, ∃ d ∈ Ioo (0 : ℝ) 1,
      ({p j, q j} : Set (ℝ × ℝ)) = {(0, d), (c, 0)} ∧ a < c ∧
      ∀ k, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
        ({p k, q k} : Set (ℝ × ℝ)) = {(0, y), (x, 0)} → ¬ (a < x ∧ x < c) := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset ι := Finset.univ.filter fun k =>
    ∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1,
      ({p k, q k} : Set (ℝ × ℝ)) = {(0, y), (x, 0)} ∧ a < x
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := hnext
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image (fun k => horizontalEndpoint (p k) (q k)) hs
  obtain ⟨c, hc, d, hd, hpair, hac⟩ := (Finset.mem_filter.mp hj).2
  refine ⟨j, c, hc, d, hd, hpair, hac, ?_⟩
  intro k x hx y hy hk hbetween
  have hks : k ∈ s := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, x, hx, y, hy, hk, hbetween.1⟩
  have hle := hmin k hks
  rw [horizontalEndpoint_eq hd.1.ne' hpair, horizontalEndpoint_eq hy.1.ne' hk] at hle
  exact (not_le_of_gt hbetween.2) hle

end PoincareConjecture.M76.TriangleCorner
