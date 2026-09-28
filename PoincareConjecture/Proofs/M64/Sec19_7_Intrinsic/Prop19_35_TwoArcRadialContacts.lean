import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerBandChords

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_near_arc_inter_trimmed_arc_subset_tip
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hinj : InjOn gamma (Icc 0 T))
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e) (hrT : ∀ e, r e ≤ T) (e : Bool) :
    ((fun s => gamma (if e then T - s else s)) '' Icc 0 (r e)) ∩
      (gamma '' Icc (r false) (T - r true)) ⊆
        {gamma (if e then T - r e else r e)} := by
  rintro z ⟨⟨s, hs, hsz⟩, t, ht, htz⟩
  have htT : t ∈ Icc (0 : ℝ) T :=
    ⟨(hr false).le.trans ht.1, ht.2.trans (sub_le_self T (hr true).le)⟩
  have hsT : (if e then T - s else s) ∈ Icc (0 : ℝ) T := by
    cases e
    · exact ⟨hs.1, hs.2.trans (hrT false)⟩
    · change T - s ∈ Icc (0 : ℝ) T
      constructor <;> linarith [hs.1, hs.2, hrT true]
  have heq := hinj hsT htT (hsz.trans htz.symm)
  apply mem_singleton_iff.mpr
  rw [← hsz]
  apply congrArg gamma
  cases e
  · change s = r false
    change s = t at heq
    linarith [ht.1, hs.2]
  · change T - s = T - r true
    change T - s = t at heq
    linarith [ht.2, hs.2]

theorem m64Intrinsic_corner_axes_inter_trimmed_arc_subset_tips
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ}
    (hai : InjOn alpha (Icc 0 A))
    (havoid : Disjoint (alpha '' Ioo 0 A) (beta '' Icc 0 B))
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e)
    (hrA : ∀ e, r e ≤ A) (hrB : ∀ e, r e ≤ B) (e : Bool)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (haxis : ∀ s : ℝ, H (s, 0) = alpha (if e then A - s else s))
    (haxis' : ∀ s : ℝ, H (0, s) = beta (if e then B - s else s)) :
    ((fun t : ℝ => H (0, t * r e)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r e, 0)) '' Icc 0 1) ∩
      (alpha '' Icc (r false) (A - r true)) ⊆ {H (r e, 0), H (0, r e)} := by
  rintro z ⟨haxes, hz⟩
  have hzopen : z ∈ alpha '' Ioo 0 A := by
    apply image_mono _ hz
    intro t ht
    exact ⟨(hr false).trans_le ht.1, ht.2.trans_lt (sub_lt_self A (hr true))⟩
  rcases haxes with ⟨t, ht, htz⟩ | ⟨t, ht, htz⟩
  · have htr : t * r e ∈ Icc (0 : ℝ) (r e) :=
      ⟨mul_nonneg ht.1 (hr e).le, mul_le_of_le_one_left (hr e).le ht.2⟩
    have hp : (if e then B - t * r e else t * r e) ∈ Icc (0 : ℝ) B := by
      cases e
      · exact ⟨htr.1, htr.2.trans (hrB false)⟩
      · change B - t * r true ∈ Icc (0 : ℝ) B
        constructor <;> linarith [htr.1, htr.2, hrB true]
    exact False.elim (disjoint_left.mp havoid hzopen
      ⟨_, hp, by simpa only [haxis'] using htz⟩)
  · have htr : t * r e ∈ Icc (0 : ℝ) (r e) :=
      ⟨mul_nonneg ht.1 (hr e).le, mul_le_of_le_one_left (hr e).le ht.2⟩
    have hnear : z ∈ (fun s => alpha (if e then A - s else s)) '' Icc 0 (r e) :=
      ⟨t * r e, htr, by simpa only [haxis] using htz⟩
    have heq := mem_singleton_iff.mp
      (m64Intrinsic_near_arc_inter_trimmed_arc_subset_tip hai r hr hrA e ⟨hnear, hz⟩)
    exact Or.inl (heq.trans (haxis (r e)).symm)

theorem m64Intrinsic_corner_axes_inter_other_trimmed_arc_subset_tips
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ}
    (hbi : InjOn beta (Icc 0 B))
    (havoid : Disjoint (beta '' Ioo 0 B) (alpha '' Icc 0 A))
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e)
    (hrA : ∀ e, r e ≤ A) (hrB : ∀ e, r e ≤ B) (e : Bool)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (haxis : ∀ s : ℝ, H (s, 0) = alpha (if e then A - s else s))
    (haxis' : ∀ s : ℝ, H (0, s) = beta (if e then B - s else s)) :
    ((fun t : ℝ => H (0, t * r e)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r e, 0)) '' Icc 0 1) ∩
      (beta '' Icc (r false) (B - r true)) ⊆ {H (r e, 0), H (0, r e)} := by
  let H' := (Homeomorph.prodComm ℝ ℝ).toOpenPartialHomeomorph.trans H
  have h := m64Intrinsic_corner_axes_inter_trimmed_arc_subset_tips
    hbi havoid r hr hrB hrA e H' haxis' haxis
  change ((fun t : ℝ => H (t * r e, 0)) '' Icc 0 1 ∪
      (fun t : ℝ => H (0, t * r e)) '' Icc 0 1) ∩
      (beta '' Icc (r false) (B - r true)) ⊆ {H (0, r e), H (r e, 0)} at h
  simpa only [union_comm, pair_comm] using h

end PoincareConjecture
