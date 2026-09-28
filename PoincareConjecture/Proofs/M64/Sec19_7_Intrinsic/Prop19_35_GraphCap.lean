import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_UpperGraph













noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture





theorem m64Intrinsic_exists_fitted_graph_cap
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) {h : ℝ → ℝ} {X : Set ℝ} {x : ℝ}
    (hX : IsOpen X) (hx : x ∈ X) (hh : ContDiffOn ℝ ∞ h X)
    {U : Set AnnulusCoordinates}
    (hgerm : ∀ᶠ z in 𝓝 (x, h x),
      (L.symm z ∈ closure U ↔ h z.1 ≤ z.2) ∧
        (L.symm z ∈ frontier U ↔ z.2 = h z.1)) :
    ∃ (a b d : ℝ) (W : Set AnnulusCoordinates),
      a < x ∧ x < b ∧ Icc a b ⊆ X ∧
      (∀ s ∈ Icc a b, h s < d) ∧
      (∀ s ∈ Icc a b, L.symm (s, h s) ∈ frontier U) ∧
      IsCompact (L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d}) ∧
      L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d} ⊆ closure U ∧
      IsOpen W ∧ L.symm (x, h x) ∈ W ∧
      W ∩ closure U ⊆
        L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d} := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hgerm
  have hR4 : 0 < R / 4 := by positivity
  have hhx := (hh x hx).continuousWithinAt.continuousAt (hX.mem_nhds hx)
  obtain ⟨e, he, heball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hX.mem_nhds hx) (hhx.preimage_mem_nhds (ball_mem_nhds (h x) hR4)))
  let r := min e (R / 4) / 2
  have hr : 0 < r := half_pos (lt_min he hR4)
  have hre : r < e := (half_lt_self (lt_min he hR4)).trans_le (min_le_left _ _)
  have hrR4 : r < R / 4 := (half_lt_self (lt_min he hR4)).trans_le (min_le_right _ _)
  have hrR : r < R := by linarith
  have hsball {s : ℝ} (hs : s ∈ Icc (x - r) (x + r)) : s ∈ ball x e := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hsX : Icc (x - r) (x + r) ⊆ X := fun s hs => (heball (hsball hs)).1
  have hsclose {s : ℝ} (hs : s ∈ Icc (x - r) (x + r)) : |h s - h x| < R / 4 := by
    exact (mem_ball.mp (heball (hsball hs)).2)
  have hgap : ∀ s ∈ Icc (x - r) (x + r), h s < h x + R / 4 := by
    intro s hs
    linarith [(abs_lt.mp (hsclose hs)).2]
  have hbandball {q : ℝ × ℝ}
      (hq : q.1 ∈ Icc (x - r) (x + r) ∧ h q.1 ≤ q.2 ∧ q.2 ≤ h x + R / 4) :
      q ∈ ball (x, h x) R := by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    constructor
    · rw [abs_lt]
      constructor <;> linarith [hq.1.1, hq.1.2]
    · rw [abs_lt]
      constructor <;> linarith [(abs_lt.mp (hsclose hq.1)).1, hq.2.1, hq.2.2]
  have hgraph : ∀ s ∈ Icc (x - r) (x + r), L.symm (s, h s) ∈ frontier U := by
    intro s hs
    exact (hball (hbandball ⟨hs, le_rfl, (hgap s hs).le⟩)).2.mpr rfl
  have hcompact : IsCompact
      {q : ℝ × ℝ | q.1 ∈ Icc (x - r) (x + r) ∧ h q.1 ≤ q.2 ∧ q.2 ≤ h x + R / 4} := by
    rw [← graphStripMap_image_rectangle hgap]
    exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      ((contDiffOn_graphStripMap hh (contDiffOn_const (c := h x + R / 4))).continuousOn.mono
        (fun q hq => ⟨hsX hq.1, mem_univ _⟩))
  let W := L.symm '' ball (x, h x) r
  refine ⟨x - r, x + r, h x + R / 4, W, by linarith, by linarith,
    hsX, hgap, hgraph, hcompact.image L.symm.continuous, ?_,
      L.symm.toHomeomorph.isOpenMap _ isOpen_ball, ⟨(x, h x), mem_ball_self hr, rfl⟩, ?_⟩
  · rintro z ⟨q, hq, rfl⟩
    exact (hball (hbandball hq)).1.mpr hq.2.1
  · rintro z ⟨⟨q, hq, rfl⟩, hz⟩
    have hqR : q ∈ ball (x, h x) R := mem_ball.mpr ((mem_ball.mp hq).trans hrR)
    have hdist : |q.1 - x| < r ∧ |q.2 - h x| < r := by
      simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using hq
    refine ⟨q, ⟨?_, (hball hqR).1.mp hz, ?_⟩, rfl⟩
    · constructor <;> linarith [(abs_lt.mp hdist.1).1, (abs_lt.mp hdist.1).2]
    · linarith [(abs_lt.mp hdist.2).2]





theorem m64Intrinsic_exists_loop_graph_cap
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ) (X : Set ℝ)
      (x a b d : ℝ) (W : Set AnnulusCoordinates),
      IsOpen X ∧ ContDiffOn ℝ ∞ h X ∧ L (gamma p) = (x, h x) ∧
      a < x ∧ x < b ∧ Icc a b ⊆ X ∧ (∀ s ∈ Icc a b, h s < d) ∧
      (∀ s ∈ Icc a b, L.symm (s, h s) ∈ frontier U) ∧
      IsCompact (L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d}) ∧
      L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d} ⊆ closure U ∧
      IsOpen W ∧ gamma p ∈ W ∧
      W ∩ closure U ⊆
        L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d} := by
  obtain ⟨L, h, X, x, hX, hx, hh, hbase, hgerm⟩ :=
    m64Intrinsic_exists_loop_upper_graph hg hend hinj hp hregular hU hV hdisj hfU hfV
  obtain ⟨a, b, d, W, ha, hb, hI, hgap, hgraph, hcompact, hsub, hW, hpW, hcover⟩ :=
    m64Intrinsic_exists_fitted_graph_cap L hX hx hh hgerm
  refine ⟨L, h, X, x, a, b, d, W, hX, hh, hbase, ha, hb, hI, hgap,
    hgraph, hcompact, hsub, hW, ?_, hcover⟩
  simpa only [← hbase, L.symm_apply_apply] using hpW

end PoincareConjecture
