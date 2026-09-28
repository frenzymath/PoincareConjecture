import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_affine_chord_image_interval
    (e : ℝ → AnnulusCoordinates)
    (he : ∀ t : ℝ, e t = (1 - t) • e 0 + t • e 1)
    {a b : ℝ} (hab : a ≤ b) :
    e '' Icc a b = segment ℝ (e a) (e b) := by
  let L : ℝ →ᵃ[ℝ] AnnulusCoordinates := AffineMap.lineMap (e 0) (e 1)
  have hL : (L : ℝ → AnnulusCoordinates) = e := by
    funext t
    rw [he t]
    dsimp [L, AffineMap.lineMap_apply]
    module
  rw [← hL, ← segment_eq_Icc hab]
  exact image_segment ℝ L a b

theorem m64Intrinsic_exists_chord_tail_neighborhood
    (e f : ℝ → AnnulusCoordinates)
    (he : ∀ t : ℝ, e t = (1 - t) • e 0 + t • e 1)
    (hinje : InjOn e (Icc (0 : ℝ) 1)) (hinjf : InjOn f (Icc (0 : ℝ) 1))
    (hsegment : f '' Icc (0 : ℝ) 1 = segment ℝ (f 0) (f 1))
    (hshared : f '' Icc (0 : ℝ) 1 ⊆ e '' Icc (0 : ℝ) 1)
    (terminal : Bool) (hbase : f 0 = e (if terminal then 1 else 0))
    (hfar : f 1 ≠ e (if terminal then 0 else 1)) :
    ∃ N : Set AnnulusCoordinates, IsOpen N ∧ f 0 ∈ N ∧
      N ∩ (e '' Icc (0 : ℝ) 1) ⊆ f '' Icc (0 : ℝ) 1 ∧ f 1 ∉ N := by
  have hecont : Continuous e := by
    have h : e = fun t : ℝ => (1 - t) • e 0 + t • e 1 := funext he
    rw [h]
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  obtain ⟨t, ht, htf⟩ := hshared ⟨1, by norm_num, rfl⟩
  have hfne : f 1 ≠ f 0 := by
    intro heq
    have h := hinjf (by norm_num) (by norm_num) heq
    norm_num at h
  cases terminal
  · change f 0 = e 0 at hbase
    change f 1 ≠ e 1 at hfar
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
      intro ht0
      apply hfne
      rw [← htf, ← ht0]
      exact hbase.symm)
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
      intro ht1
      exact hfar (htf.symm.trans (congrArg e ht1)))
    let tail := e '' Icc t 1
    have hcompact : IsCompact tail := isCompact_Icc.image hecont
    have hbaseNot : f 0 ∉ tail := by
      rintro ⟨s, hs, hsf⟩
      have hs0 := hinje ⟨ht0.le.trans hs.1, hs.2⟩ (by norm_num) (hsf.trans hbase)
      linarith [hs.1]
    have hcut : e '' Icc 0 t = f '' Icc (0 : ℝ) 1 := by
      rw [m64Intrinsic_affine_chord_image_interval e he ht0.le, hsegment, hbase, htf]
    refine ⟨tailᶜ, hcompact.isClosed.isOpen_compl, hbaseNot, ?_, ?_⟩
    · rintro z ⟨hzN, s, hs, rfl⟩
      have hst : s < t := by
        by_contra hn
        exact hzN ⟨s, ⟨le_of_not_gt hn, hs.2⟩, rfl⟩
      rw [← hcut]
      exact ⟨s, ⟨hs.1, hst.le⟩, rfl⟩
    · intro hnot
      exact hnot ⟨t, ⟨le_rfl, ht1.le⟩, htf⟩
  · change f 0 = e 1 at hbase
    change f 1 ≠ e 0 at hfar
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
      intro ht0
      exact hfar (htf.symm.trans (congrArg e ht0.symm)))
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
      intro ht1
      apply hfne
      rw [← htf, ht1]
      exact hbase.symm)
    let tail := e '' Icc 0 t
    have hcompact : IsCompact tail := isCompact_Icc.image hecont
    have hbaseNot : f 0 ∉ tail := by
      rintro ⟨s, hs, hsf⟩
      have hs1 := hinje ⟨hs.1, hs.2.trans ht1.le⟩ (by norm_num) (hsf.trans hbase)
      linarith [hs.2]
    have hcut : e '' Icc t 1 = f '' Icc (0 : ℝ) 1 := by
      rw [m64Intrinsic_affine_chord_image_interval e he ht1.le, hsegment, hbase, htf]
      exact segment_symm ℝ _ _
    refine ⟨tailᶜ, hcompact.isClosed.isOpen_compl, hbaseNot, ?_, ?_⟩
    · rintro z ⟨hzN, s, hs, rfl⟩
      have hst : t < s := by
        by_contra hn
        exact hzN ⟨s, ⟨hs.1, le_of_not_gt hn⟩, rfl⟩
      rw [← hcut]
      exact ⟨s, ⟨hst.le, hs.2⟩, rfl⟩
    · intro hnot
      exact hnot ⟨t, ⟨ht0.le, le_rfl⟩, htf⟩

end PoincareConjecture
