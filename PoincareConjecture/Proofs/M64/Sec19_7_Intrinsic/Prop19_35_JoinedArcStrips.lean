import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseArcCuts

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_exists_joined_arc_strips
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (v w : AnnulusCoordinates)
    (hpa : ∀ t ∈ Icc a b, 0 < inner ℝ v (deriv alpha t))
    (hpb : ∀ t ∈ Icc c d, 0 < inner ℝ v (deriv beta t))
    (hta : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv alpha t)) w)
    (htb : ∀ t ∈ Icc c d, 0 < inner ℝ (quarterTurn (deriv beta t)) w)
    (hend : alpha b = beta c)
    (hmeet : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
      alpha s = beta t → s = b ∧ t = c) :
    ∃ (L R : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G H : OpenPartialHomeomorph ℝ ℝ) (f g : ℝ → ℝ)
      (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
      (P : TransverseGraphCuts f (G a) (G b) (L w).1 (L w).2 (L w).1 (L w).2)
      (Q : TransverseGraphCuts g (H c) (H d) (R w).1 (R w).2 (R w).1 (R w).2),
      let S := P.linearCoordinates L.symm G.open_target hf
      let T := Q.linearCoordinates R.symm H.open_target hg
      ∃ delta > 0, delta ≤ P.radius ∧ delta ≤ Q.radius ∧
        (Icc a b ⊆ G.source ∧ StrictMonoOn G G.source ∧
          ContDiffOn ℝ ∞ G G.source ∧
          (∀ t ∈ G.source, L (alpha t) = (G t, f (G t))) ∧
          G '' Icc a b = Icc (G a) (G b) ∧ Icc (G a) (G b) ⊆ G.target) ∧
        (Icc c d ⊆ H.source ∧ StrictMonoOn H H.source ∧
          ContDiffOn ℝ ∞ H H.source ∧
          (∀ t ∈ H.source, R (beta t) = (H t, g (H t))) ∧
          H '' Icc c d = Icc (H c) (H d) ∧ Icc (H c) (H d) ⊆ H.target) ∧
        ((fun t => S (t, 0)) '' Icc (0 : ℝ) 1 = alpha '' Icc a b) ∧
        ((fun t => T (t, 0)) '' Icc (0 : ℝ) 1 = beta '' Icc c d) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ z y : ℝ, |z| < delta → |y| < delta →
            (t, z) ∈ S.source ∧ (s, y) ∈ T.source ∧
              (S (t, z) = T (s, y) → t = 1 ∧ s = 0)) ∧
        ∀ h k : ℝ → ℝ,
          (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ h t ∧ h t < delta) →
          (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ k t ∧ k t < delta) →
          ∀ r : ℝ, 0 ≤ r → r ∈ P.right.parameter.source → r ∈ Q.left.parameter.source →
            h 1 = P.right.parameter r → k 0 = Q.left.parameter r →
            S '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
              T '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ k q.1} =
                segment ℝ (alpha b) (alpha b + r • w) := by
  obtain ⟨L, G, f, hI, hG, hGs, hf, hgraph, himage, htarget, htrans, ⟨P⟩⟩ :=
    m64Intrinsic_exists_arc_transverse_graph ha hab hpa (fun _ => w) hta
  obtain ⟨R, H, g, hJ, hH, hHs, hg, hgraph', himage', htarget', htrans', ⟨Q⟩⟩ :=
    m64Intrinsic_exists_arc_transverse_graph hb hcd hpb (fun _ => w) htb
  have haG := hI (left_mem_Icc.mpr hab.le)
  have hbG := hI (right_mem_Icc.mpr hab.le)
  have hcH := hJ (left_mem_Icc.mpr hcd.le)
  have hdH := hJ (right_mem_Icc.mpr hcd.le)
  have hbase : ∀ x ∈ Icc (G a) (G b), ∀ y ∈ Icc (H c) (H d),
      L.symm (x, f x) = R.symm (y, g y) → x = G b ∧ y = H c := by
    intro x hx y hy heq
    obtain ⟨s, hs, rfl⟩ := (himage ▸ hx : x ∈ G '' Icc a b)
    obtain ⟨t, ht, rfl⟩ := (himage' ▸ hy : y ∈ H '' Icc c d)
    rw [← hgraph s (hI hs), ← hgraph' t (hJ ht),
      L.symm_apply_apply, R.symm_apply_apply] at heq
    obtain ⟨rfl, rfl⟩ := hmeet s hs t ht heq
    exact ⟨rfl, rfl⟩
  have hp : L.symm (G b, f (G b)) = alpha b := by
    rw [← hgraph b hbG, L.symm_apply_apply]
  have hq : R.symm (H c, g (H c)) = beta c := by
    rw [← hgraph' c hcH, R.symm_apply_apply]
  obtain ⟨delta, hdelta, hdP, hdQ, hsep, hinter⟩ :=
    exists_adjacent_linear_oblique_intersection P Q L.symm R.symm
      G.open_target hf H.open_target hg (hG haG hbG hab) htarget
      (hH hcH hdH hcd) htarget' (by rw [hp, hq, hend])
      (by simp only [Prod.eta, L.symm_apply_apply, R.symm_apply_apply]) hbase
      (innerSL ℝ (-quarterTurn w))
      (by
        simp only [Prod.eta, L.symm_apply_apply]
        change inner ℝ (-quarterTurn w) w = 0
        exact (htrans b (right_mem_Icc.mpr hab.le)).2.1)
      (htrans b (right_mem_Icc.mpr hab.le)).2.2
      (htrans' c (left_mem_Icc.mpr hcd.le)).2.2
  refine ⟨L, R, G, H, f, g, hf, hg, P, Q, delta, hdelta, hdP, hdQ,
    ⟨hI, hG, hGs, hgraph, himage, htarget⟩,
    ⟨hJ, hH, hHs, hgraph', himage', htarget'⟩, ?_, ?_, hsep, ?_⟩
  · exact m64Intrinsic_graph_strip_axis_image L G hf hI (hG haG hbG hab).le
      hgraph himage P
  · exact m64Intrinsic_graph_strip_axis_image R H hg hJ (hH hcH hdH hcd).le
      hgraph' himage' Q
  · intro h k hh hk r hr hrP hrQ hhend hkend
    simpa only [hp, Prod.eta, L.symm_apply_apply] using
      hinter h k hh hk r hr hrP hrQ hhend hkend

end PoincareConjecture
