import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_nonnested_disc_transition
    (U V : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (hU : ContDiffOn ℝ ∞ U U.source)
    (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source)
    (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (hUh : ∀ p ∈ U.source, (U p).2 = p.2)
    (hVh : ∀ p ∈ V.source, (V p).2 = p.2)
    (a l r b : ℝ) (hal : a < l) (hlr : l < r) (hrb : r < b)
    (hUs : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ U.source)
    (hVs : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ V.source)
    (hboundary : ∀ z ∈ Icc a b,
      (fun x : E2 => (U (x, z)).1) '' sphere 0 1 =
        (fun x : E2 => (V (x, z)).1) '' sphere 0 1) :
    ∃ (k : ℝ → ℝ) (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ)),
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc a b) ∧
      EqOn k id (Icc l r) ∧
      e.source = {p | (p.1, k p.2) ∈ (V.trans U.symm).source} ∧
      e.target = {p | (p.1, k p.2) ∈ (V.trans U.symm).target} ∧
      (∀ p, e p = ((U.symm (V (p.1, k p.2))).1, p.2)) ∧
      (∀ p, e.symm p = ((V.symm (U (p.1, k p.2))).1, p.2)) ∧
      ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, (e p).2 = p.2) ∧
      (∀ p, (e.symm p).2 = p.2) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.source ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.target ∧
      (∀ z : ℝ, ∀ A : Set E2,
        (A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) →
        e '' (A ×ˢ ({z} : Set ℝ)) = A ×ˢ ({z} : Set ℝ) ∧
        e.symm '' (A ×ˢ ({z} : Set ℝ)) = A ×ˢ ({z} : Set ℝ) ∧
        (∀ x ∈ A, (e (x, z)).1 ∈ A) ∧
        (∀ y ∈ A, (e.symm (y, z)).1 ∈ A) ∧
        (∀ p ∈ (V.trans U.symm).source, p.2 ∈ Icc l r →
          e p = (V.trans U.symm) p) ∧
        (∀ p ∈ (V.trans U.symm).target, p.2 ∈ Icc l r →
          (e.symm p) = ((V.trans U.symm).symm p))) := by
  classical
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hUih (p : E2 × ℝ) (hp : p ∈ U.target) : (U.symm p).2 = p.2 := by
    have h := hUh (U.symm p) (U.map_target hp)
    rw [U.right_inv hp] at h
    exact h.symm
  have hVih (p : E2 × ℝ) (hp : p ∈ V.target) : (V.symm p).2 = p.2 := by
    have h := hVh (V.symm p) (V.map_target hp)
    rw [V.right_inv hp] at h
    exact h.symm
  have hAsub (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      A ⊆ closedBall (0 : E2) 1 := by
    rcases hA with rfl | rfl | rfl
    · exact ball_subset_closedBall
    · exact subset_rfl
    · exact sphere_subset_closedBall
  have hregion (z : ℝ) (hz : z ∈ Icc a b) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (fun x : E2 => (U (x, z)).1) '' A =
        (fun x : E2 => (V (x, z)).1) '' A := by
    obtain ⟨BU, hBU, _, _, _⟩ := exists_saddle_end_fiber_chart U hU hUi hUh z
      (fun x hx => hUs ⟨hx, hz⟩)
    obtain ⟨BV, hBV, _, _, _⟩ := exists_saddle_end_fiber_chart V hV hVi hVh z
      (fun x hx => hVs ⟨hx, hz⟩)
    have hBUimage (S : Set E2) : BU.chart '' S =
        (fun x : E2 => (U (x, z)).1) '' S :=
      image_congr (fun x _ => hBU x)
    have hBVimage (S : Set E2) : BV.chart '' S =
        (fun x : E2 => (V (x, z)).1) '' S :=
      image_congr (fun x _ => hBV x)
    have hbound : BU.boundary = BV.boundary := by
      change BU.chart '' sphere 0 1 = BV.chart '' sphere 0 1
      rw [hBUimage, hBVimage, hboundary z hz]
    have hins := BU.inside_eq_of_boundary_eq BV hdim hbound
    have hclosed := BU.closedRegion_eq_of_boundary_eq BV hdim hbound
    rcases hA with rfl | rfl | rfl
    · change (fun x : E2 => (U (x, z)).1) '' ball 0 1 = _
      rw [← hBUimage (ball 0 1), ← hBVimage (ball 0 1)]
      simpa only [BallNeighborhoodChart.inside] using hins
    · change (fun x : E2 => (U (x, z)).1) '' closedBall 0 1 = _
      rw [← hBUimage (closedBall 0 1), ← hBVimage (closedBall 0 1)]
      simpa only [BallNeighborhoodChart.closedRegion] using hclosed
    · change (fun x : E2 => (U (x, z)).1) '' sphere 0 1 = _
      rw [← hBUimage (sphere 0 1), ← hBVimage (sphere 0 1)]
      simpa only [BallNeighborhoodChart.boundary] using hbound
  let E := V.trans U.symm
  have hEheight (p : E2 × ℝ) (hp : p ∈ E.source) : (E p).2 = p.2 := by
    change (U.symm (V p)).2 = p.2
    exact (hUih (V p) hp.2).trans (hVh p hp.1)
  have hEheighti (p : E2 × ℝ) (hp : p ∈ E.target) :
      (E.symm p).2 = p.2 := by
    change (V.symm (U p)).2 = p.2
    exact (hVih (U p) hp.2).trans (hUh p hp.1)
  have hEcyl : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ E.source := by
    intro p hp
    have hpV : p ∈ V.source := hVs hp
    have himg : (V p).1 ∈ (fun x : E2 => (U (x, p.2)).1) ''
        closedBall 0 1 := by
      rw [hregion p.2 hp.2 (closedBall (0 : E2) 1) (Or.inr (Or.inl rfl))]
      exact ⟨p.1, hp.1, rfl⟩
    rcases himg with ⟨y, hy, hyeq⟩
    have hyU : (y, p.2) ∈ U.source := hUs ⟨hy, hp.2⟩
    have heq : U (y, p.2) = V p := by
      apply Prod.ext
      · exact hyeq
      · exact (hUh (y, p.2) hyU).trans (hVh p hpV).symm
    change p ∈ V.source ∧ V p ∈ U.target
    refine ⟨hpV, ?_⟩
    rw [← heq]
    exact U.map_source hyU
  have hEcyl' : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ E.target := by
    intro p hp
    have hpU : p ∈ U.source := hUs hp
    have himg : (U p).1 ∈ (fun x : E2 => (V (x, p.2)).1) ''
        closedBall 0 1 := by
      rw [← hregion p.2 hp.2 (closedBall (0 : E2) 1) (Or.inr (Or.inl rfl))]
      exact ⟨p.1, hp.1, rfl⟩
    rcases himg with ⟨y, hy, hyeq⟩
    have hyV : (y, p.2) ∈ V.source := hVs ⟨hy, hp.2⟩
    have heq : V (y, p.2) = U p := by
      apply Prod.ext
      · exact hyeq
      · exact (hVh (y, p.2) hyV).trans (hUh p hpU).symm
    change p ∈ U.source ∧ U p ∈ V.target
    refine ⟨hpU, ?_⟩
    rw [← heq]
    exact V.map_source hyV
  have hEmove (z : ℝ) (hz : z ∈ Icc a b) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (∀ x ∈ A, (x, z) ∈ E.source ∧ (E (x, z)).1 ∈ A) ∧
      (∀ y ∈ A, (y, z) ∈ E.target ∧ (E.symm (y, z)).1 ∈ A) := by
    have hsub := hAsub A hA
    have hreg := hregion z hz A hA
    constructor
    · intro x hx
      have hxs := hEcyl (show (x, z) ∈ closedBall (0 : E2) 1 ×ˢ Icc a b from
        ⟨hsub hx, hz⟩)
      have himg : (V (x, z)).1 ∈
          (fun y : E2 => (U (y, z)).1) '' A := by
        rw [hreg]
        exact ⟨x, hx, rfl⟩
      rcases himg with ⟨y, hy, hyeq⟩
      have hys : (y, z) ∈ U.source := hUs (show (y, z) ∈
        closedBall (0 : E2) 1 ×ˢ Icc a b from ⟨hsub hy, hz⟩)
      have heq : U (y, z) = V (x, z) := by
        apply Prod.ext
        · exact hyeq
        · exact (hUh (y, z) hys).trans (hVh (x, z) (hVs ⟨hsub hx, hz⟩)).symm
      refine ⟨hxs, ?_⟩
      change (U.symm (V (x, z))).1 ∈ A
      rw [← heq, U.left_inv hys]
      exact hy
    · intro y hy
      have hys := hEcyl' (show (y, z) ∈ closedBall (0 : E2) 1 ×ˢ Icc a b from
        ⟨hsub hy, hz⟩)
      have himg : (U (y, z)).1 ∈
          (fun x : E2 => (V (x, z)).1) '' A := by
        rw [← hreg]
        exact ⟨y, hy, rfl⟩
      rcases himg with ⟨x, hx, hxeq⟩
      have hxs : (x, z) ∈ V.source := hVs (show (x, z) ∈
        closedBall (0 : E2) 1 ×ˢ Icc a b from ⟨hsub hx, hz⟩)
      have heq : V (x, z) = U (y, z) := by
        apply Prod.ext
        · exact hxeq
        · exact (hVh (x, z) hxs).trans (hUh (y, z) (hUs (show (y, z) ∈
            closedBall (0 : E2) 1 ×ˢ Icc a b from ⟨hsub hy, hz⟩))).symm
      refine ⟨hys, ?_⟩
      change (V.symm (U (y, z))).1 ∈ A
      rw [← heq, V.left_inv hxs]
      exact hx
  let d := min (l - a) (b - r) / 2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  obtain ⟨k, hk, hkrange, hkfix⟩ := exists_saddle_end_height_clamp l r d hlr hd
  have hkI (z : ℝ) : k z ∈ Icc a b := by
    have hz := hkrange z
    have hdl : d ≤ l - a := by
      dsimp [d]
      have hh := min_le_left (l - a) (b - r)
      linarith
    have hdr : d ≤ b - r := by
      dsimp [d]
      have hh := min_le_right (l - a) (b - r)
      linarith
    constructor <;> linarith [hz.1, hz.2, hdl, hdr]
  have hE : ContDiffOn ℝ ∞ E E.source := by
    change ContDiffOn ℝ ∞ (fun p => U.symm (V p))
      (V.source ∩ V ⁻¹' U.target)
    have hV' : ContDiffOn ℝ ∞ V (V.source ∩ V ⁻¹' U.target) :=
      hV.mono inter_subset_left
    exact hUi.comp hV' (fun _ hp => hp.2)
  have hEi : ContDiffOn ℝ ∞ E.symm E.target := by
    change ContDiffOn ℝ ∞ (fun p => V.symm (U p))
      (U.source ∩ U ⁻¹' V.target)
    have hU' : ContDiffOn ℝ ∞ U (U.source ∩ U ⁻¹' V.target) :=
      hU.mono inter_subset_left
    exact hVi.comp hU' (fun _ hp => hp.2)
  obtain ⟨e, heapply, heinv, hesource, hetarget, he, hei, heh⟩ :=
    exists_saddle_end_chart_reparam E hE hEi hEheight k hk
  have heih (p : E2 × ℝ) (hp : p ∈ e.target) : (e.symm p).2 = p.2 := by
    have hh := heh (e.symm p)
    rw [e.right_inv hp] at hh
    exact hh.symm
  have hecyl : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.source := by
    intro p hp
    rw [hesource]
    exact hEcyl ⟨hp.1, hkI p.2⟩
  have hecyl' : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.target := by
    intro p hp
    rw [hetarget]
    exact hEcyl' ⟨hp.1, hkI p.2⟩
  have hemove (z : ℝ) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (∀ x ∈ A, (x, z) ∈ e.source ∧ (e (x, z)).1 ∈ A) ∧
      (∀ y ∈ A, (y, z) ∈ e.target ∧ (e.symm (y, z)).1 ∈ A) := by
    have h := hEmove (k z) (hkI z) A hA
    constructor
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [hesource]
        exact h.1 x hx |>.1
      · rw [heapply]
        exact h.1 x hx |>.2
    · intro y hy
      refine ⟨?_, ?_⟩
      · rw [hetarget]
        exact h.2 y hy |>.1
      · rw [heinv]
        exact h.2 y hy |>.2
  have heimage (z : ℝ) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      e '' (A ×ˢ ({z} : Set ℝ)) = A ×ˢ ({z} : Set ℝ) ∧
      e.symm '' (A ×ˢ ({z} : Set ℝ)) = A ×ˢ ({z} : Set ℝ) := by
    have hf := hemove z A hA
    constructor
    · ext p
      constructor
      · rintro ⟨⟨x, t⟩, hq, rfl⟩
        have ht : t = z := by simpa using hq.2
        subst t
        have hm := (hemove z A hA).1 x hq.1
        exact ⟨hm.2, by simp [heh]⟩
      · rintro ⟨hy, _ht⟩
        rcases p with ⟨y, t⟩
        have ht : t = z := by simpa using _ht
        subst t
        have hm := (hemove z A hA).2 y hy
        refine ⟨e.symm (y, z), ⟨hm.2, by simp [heih (y, z) hm.1]⟩, ?_⟩
        exact e.right_inv hm.1
    · ext p
      constructor
      · rintro ⟨⟨x, t⟩, hq, rfl⟩
        have ht : t = z := by simpa using hq.2
        subst t
        have hm := (hemove z A hA).2 x hq.1
        exact ⟨hm.2, by simp [heih (x, z) hm.1]⟩
      · rintro ⟨hy, _ht⟩
        rcases p with ⟨y, t⟩
        have ht : t = z := by simpa using _ht
        subst t
        have hm := (hemove z A hA).1 y hy
        refine ⟨e (y, z), ⟨hm.2, by simp [heh]⟩, ?_⟩
        exact e.left_inv hm.1
  have heih' (p : E2 × ℝ) : (e.symm p).2 = p.2 := by
    rw [heinv]
  refine ⟨k, e, hk, hkI, hkfix, hesource, hetarget, ?_, ?_, he, hei,
    heh, heih', hecyl, hecyl', ?_⟩
  · intro p
    rw [heapply]
    rfl
  · intro p
    rw [heinv]
    rfl
  · intro z A hA
    refine ⟨(heimage z A hA).1, (heimage z A hA).2,
      ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact hemove z A hA |>.1 x hx |>.2
    · intro y hy
      exact hemove z A hA |>.2 y hy |>.2
    · intro p hp hz
      rw [heapply, hkfix hz]
      change ((U.symm (V (p.1, p.2))).1, p.2) = (V.trans U.symm) p
      rw [OpenPartialHomeomorph.trans_apply]
      exact Prod.ext rfl (hEheight p hp).symm
    · intro p hp hz
      rw [heinv, hkfix hz]
      change ((V.symm (U (p.1, p.2))).1, p.2) = (V.trans U.symm).symm p
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply]
      exact Prod.ext rfl (hEheighti p hp).symm

end PoincareConjecture.M25.Topology3D
