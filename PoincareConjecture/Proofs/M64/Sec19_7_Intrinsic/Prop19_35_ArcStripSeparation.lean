import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcNormalCuts
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.DisjointStrips

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_graph_strip_axis_image
    {gamma : ℝ → AnnulusCoordinates}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f G.target) {a b : ℝ}
    (hI : Icc a b ⊆ G.source) (hab : G a ≤ G b)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    {ua wa ub wb : ℝ} (P : TransverseGraphCuts f (G a) (G b) ua wa ub wb) :
    (fun t => P.linearCoordinates L.symm G.open_target hf (t, 0)) '' Icc (0 : ℝ) 1 =
      gamma '' Icc a b := by
  have hparam : (fun t : ℝ => G a + t * (G b - G a)) '' Icc (0 : ℝ) 1 =
      Icc (G a) (G b) := by
    have heq : (fun t : ℝ => G a + t * (G b - G a)) =
        AffineMap.lineMap (G a) (G b) := by
      funext t
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      ring
    rw [heq, ← segment_eq_image_lineMap, segment_eq_Icc hab]
  calc
    _ = (fun x => L.symm (x, f x)) ''
        ((fun t : ℝ => G a + t * (G b - G a)) '' Icc (0 : ℝ) 1) := by
      rw [image_image]
      exact image_congr (fun t _ => P.linearCoordinates_axis L.symm G.open_target hf t)
    _ = (fun t => L.symm (G t, f (G t))) '' Icc a b := by
      rw [hparam, ← himage, image_image]
    _ = _ := image_congr (fun t ht => by rw [← hgraph t (hI ht), L.symm_apply_apply])

theorem m64Intrinsic_adjacent_normal_strip_width
    {gamma : ℝ → AnnulusCoordinates} {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hinj : InjOn gamma (Icc a c))
    (L R : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G H : OpenPartialHomeomorph ℝ ℝ) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
    (hI : Icc a b ⊆ G.source) (hJ : Icc b c ⊆ H.source)
    (hG : StrictMonoOn G G.source) (hH : StrictMonoOn H H.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (hgraph' : ∀ t ∈ H.source, R (gamma t) = (H t, g (H t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    (himage' : H '' Icc b c = Icc (H b) (H c))
    (htarget : Icc (G a) (G b) ⊆ G.target)
    (htarget' : Icc (H b) (H c) ⊆ H.target)
    (hsep : 0 < inner ℝ (deriv gamma b) (L.symm (1, deriv f (G b))))
    (hsep' : 0 < inner ℝ (deriv gamma b) (R.symm (1, deriv g (H b))))
    (P : TransverseGraphCuts f (G a) (G b)
      (L (quarterTurn (deriv gamma a))).1 (L (quarterTurn (deriv gamma a))).2
      (L (quarterTurn (deriv gamma b))).1 (L (quarterTurn (deriv gamma b))).2)
    (Q : TransverseGraphCuts g (H b) (H c)
      (R (quarterTurn (deriv gamma b))).1 (R (quarterTurn (deriv gamma b))).2
      (R (quarterTurn (deriv gamma c))).1 (R (quarterTurn (deriv gamma c))).2) :
    ∃ delta > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < delta → |w| < delta →
        (t, z) ∈ (P.linearCoordinates L.symm G.open_target hf).source ∧
        (s, w) ∈ (Q.linearCoordinates R.symm H.open_target hg).source ∧
        (P.linearCoordinates L.symm G.open_target hf (t, z) =
            Q.linearCoordinates R.symm H.open_target hg (s, w) → t = 1 ∧ s = 0) := by
  have haG := hI (left_mem_Icc.mpr hab.le)
  have hbG := hI (right_mem_Icc.mpr hab.le)
  have hbH := hJ (left_mem_Icc.mpr hbc.le)
  have hcH := hJ (right_mem_Icc.mpr hbc.le)
  apply exists_adjacent_linear_oblique_width P Q L.symm R.symm G.open_target hf
    H.open_target hg (hG haG hbG hab) htarget (hH hbH hcH hbc) htarget'
      (by rw [← hgraph b hbG, ← hgraph' b hbH, L.symm_apply_apply, R.symm_apply_apply])
      (by simp only [Prod.eta, L.symm_apply_apply, R.symm_apply_apply]) ?_
      (innerSL ℝ (deriv gamma b)) ?_ hsep hsep'
  · intro x hx y hy heq
    obtain ⟨u, hu, rfl⟩ := (himage ▸ hx : x ∈ G '' Icc a b)
    obtain ⟨v, hv, rfl⟩ := (himage' ▸ hy : y ∈ H '' Icc b c)
    rw [← hgraph u (hI hu), ← hgraph' v (hJ hv),
      L.symm_apply_apply, R.symm_apply_apply] at heq
    have huv := hinj ⟨hu.1, hu.2.trans hbc.le⟩ ⟨hab.le.trans hv.1, hv.2⟩ heq
    have hub : u = b := le_antisymm hu.2 (huv ▸ hv.1)
    have hvb : v = b := huv.symm.trans hub
    simp only [hub, hvb, and_self]
  · simp only [Prod.eta, L.symm_apply_apply]
    exact inner_quarterTurn_self (deriv gamma b)

end PoincareConjecture
