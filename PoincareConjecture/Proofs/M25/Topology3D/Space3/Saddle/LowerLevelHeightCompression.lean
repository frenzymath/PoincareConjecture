import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceHeightCompression











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D1" => Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




noncomputable def SaddleLowerLevelData.heightCompress
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    {D : SaddlePieceData psi u} (W : SaddleLowerLevelData D) (hpsi : IsCollarEmbedding psi)
    (h : D1) (G0 G : D3) (k delta : ℝ)
    (R o w : Fin D.capCount → ℝ) (hk : 0 < k) (hdelta : 0 < delta)
    (hmono : StrictMono (fun z => h z))
    (hfix : ∀ z, |z - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤ delta → h z = z)
    (hG0 : ∀ y : E3, ⟪(u : E3), G0 y⟫_ℝ = h ⟪(u : E3), y⟫_ℝ)
    (hRadius : ∀ i, D.cutRadius i ≤ R i)
    (hWidths : ∀ i, 0 < o i ∧ o i ≤ (D.cap i).overlapWidth / 4 ∧
      0 < w i ∧ w i ≤ (D.cap i).collarWidth / 4)
    (hAffine : ∀ i z, |z - (D.cap i).cutHeight| ≤ R i →
      h z = ⟪(u : E3), psi (D.point, 0)⟫_ℝ +
        k * (z - ⟪(u : E3), psi (D.point, 0)⟫_ℝ))
    (hCap : ∀ i (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 ≤ 2 * o i →
      |(D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model q).2) -
        (D.cap i).cutHeight| ≤ R i)
    (hCol : ∀ i s, |s| ≤ 2 * w i →
      |(D.cap i).cutHeight + (D.cap i).sign * ((D.cap i).removal - (D.cap i).scale) +
        (D.cap i).beta * s - (D.cap i).cutHeight| ≤ R i)
    (hAgree : EqOn G G0 (range (fun q : UnitTwoSphere => psi (q, 0)) ∪
      ⋃ i, (D.cap i).tube '' (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i))))
    (hPlanar : ∀ y : E3, (heightPlaneCoordinates u (G y)).1 = (heightPlaneCoordinates u y).1) :
    SaddleLowerLevelData (D.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
      hfix hG0 hRadius hWidths hAffine hCap hCol hAgree) := by
  let H := (Diffeomorph.refl (𝓡 1) UnitCircle ∞).prodCongr h.symm
  let L (b : Fin 2) := H.toHomeomorph.toOpenPartialHomeomorph.trans (W.leg b)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  have hnew (q : UnitTwoSphere) : ⟪(u : E3), G (psi (q, 0))⟫_ℝ = h (f q) := by
    rw [hAgree (Or.inl (mem_range_self q)), hG0]
  have hseam (i : Fin D.capCount) :
      h (D.cap i).cutHeight + (D.cap i).sign * (k * (D.cap i).removal) =
        h ((D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal) := by
    have hR : 0 < R i :=
      ((D.cap i).removal_pos.trans (D.removal_lt_cutRadius i)).trans_le (hRadius i)
    have hwin : |(D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal -
        (D.cap i).cutHeight| ≤ R i := by
      rw [add_sub_cancel_left, abs_mul, (D.cap i).sign_abs, one_mul,
        abs_of_pos (D.cap i).removal_pos]
      exact (D.removal_lt_cutRadius i).le.trans (hRadius i)
    rw [hAffine i _ (by simpa only [sub_self, abs_zero] using hR.le), hAffine i _ hwin]
    ring
  have hIcc (a b z : ℝ) : z ∈ Icc (h a) (h b) ↔ h.symm z ∈ Icc a b := by
    constructor
    · intro hz
      exact ⟨hmono.le_iff_le.mp (by simpa only [h.apply_symm_apply] using hz.1),
        hmono.le_iff_le.mp (by simpa only [h.apply_symm_apply] using hz.2)⟩
    · intro hz
      exact ⟨by simpa only [h.apply_symm_apply] using hmono.monotone hz.1,
        by simpa only [h.apply_symm_apply] using hmono.monotone hz.2⟩
  have hsource (b : Fin 2) (p : UnitCircle × ℝ) :
      p ∈ (L b).source ↔ (p.1, h.symm p.2) ∈ (W.leg b).source := by
    change (True ∧ (p.1, h.symm p.2) ∈ (W.leg b).source) ↔ _
    simp only [true_and]
  have htrack (b : Fin 2) :
      L b '' (univ ×ˢ Icc
        (h (D.cap (W.label b)).cutHeight +
          (D.cap (W.label b)).sign * (k * (D.cap (W.label b)).removal)) (h W.level)) =
      W.leg b '' (univ ×ˢ Icc
        ((D.cap (W.label b)).cutHeight +
          (D.cap (W.label b)).sign * (D.cap (W.label b)).removal) W.level) := by
    rw [hseam]
    ext q
    constructor
    · rintro ⟨⟨theta, z⟩, hp, rfl⟩
      exact ⟨(theta, h.symm z), ⟨mem_univ _, (hIcc _ _ _).mp hp.2⟩, rfl⟩
    · rintro ⟨⟨theta, z⟩, hp, rfl⟩
      refine ⟨(theta, h z), ⟨mem_univ _, hmono.monotone hp.2.1,
        hmono.monotone hp.2.2⟩, ?_⟩
      change W.leg b (theta, h.symm (h z)) = W.leg b (theta, z)
      rw [h.symm_apply_apply]
  exact {
    level := h W.level
    level_lt_critical := by
      change h W.level < ⟪(u : E3), G (psi (D.point, 0))⟫_ℝ
      rw [hnew D.point]
      exact hmono W.level_lt_critical
    lower_seams_lt_level := by
      change ∀ i : Fin D.capCount, (D.cap i).sign = 1 →
        h (D.cap i).cutHeight + (D.cap i).sign * (k * (D.cap i).removal) < h W.level
      intro i hi
      rw [hseam]
      exact hmono (W.lower_seams_lt_level i hi)
    label := W.label
    label_injective := W.label_injective
    label_lower := W.label_lower
    leg := L
    leg_source := by
      intro b p hp
      change p ∈ univ ×ˢ Icc (h (D.cap (W.label b)).cutHeight +
        (D.cap (W.label b)).sign * (k * (D.cap (W.label b)).removal)) (h W.level) at hp
      apply (hsource b p).mpr
      apply W.leg_source b
      refine ⟨mem_univ _, (hIcc _ _ _).mp ?_⟩
      simpa only [hseam] using hp.2
    leg_smooth := by
      intro b
      exact (W.leg_smooth b).comp H.contMDiff.contMDiffOn
        (fun p hp => (hsource b p).mp hp)
    leg_inverse := by
      intro b
      exact H.symm.contMDiff.comp_contMDiffOn ((W.leg_inverse b).mono (fun _ hp => hp.1))
    leg_height := by
      intro b p hp
      rw [hnew]
      change h ⟪(u : E3), psi (W.leg b (p.1, h.symm p.2), 0)⟫_ℝ = p.2
      rw [W.leg_height b _ ((hsource b p).mp hp), h.apply_symm_apply]
    leg_bottom := by
      intro b
      change range (fun theta => L b (theta, h (D.cap (W.label b)).cutHeight +
        (D.cap (W.label b)).sign * (k * (D.cap (W.label b)).removal))) =
        (D.cap (W.label b)).sourceSeam
      rw [hseam]
      change range (fun theta => W.leg b
        (theta, h.symm (h ((D.cap (W.label b)).cutHeight +
          (D.cap (W.label b)).sign * (D.cap (W.label b)).removal)))) =
        (D.cap (W.label b)).sourceSeam
      simpa only [h.symm_apply_apply] using W.leg_bottom b
    leg_disjoint := by
      change Disjoint
        (L 0 '' (univ ×ˢ Icc (h (D.cap (W.label 0)).cutHeight +
          (D.cap (W.label 0)).sign * (k * (D.cap (W.label 0)).removal)) (h W.level)))
        (L 1 '' (univ ×ˢ Icc (h (D.cap (W.label 1)).cutHeight +
          (D.cap (W.label 1)).sign * (k * (D.cap (W.label 1)).removal)) (h W.level)))
      rw [htrack 0, htrack 1]
      exact W.leg_disjoint
    leg_cover := by
      change (⋃ b, L b '' (univ ×ˢ Icc (h (D.cap (W.label b)).cutHeight +
        (D.cap (W.label b)).sign * (k * (D.cap (W.label b)).removal)) (h W.level))) =
        D.sourceCore ∩ {q | ⟪(u : E3), G (psi (q, 0))⟫_ℝ ≤ h W.level}
      simp only [htrack]
      rw [W.leg_cover]
      ext q
      change (q ∈ D.sourceCore ∧ f q ≤ W.level) ↔
        (q ∈ D.sourceCore ∧ ⟪(u : E3), G (psi (q, 0))⟫_ℝ ≤ h W.level)
      rw [hnew q, hmono.le_iff_le]
    disc := W.disc
    disc_boundary := by
      intro b
      change (fun x => (heightPlaneCoordinates u).symm (x, h W.level)) ''
        (W.disc b).boundary = range (fun theta =>
          G (psi (W.leg b (theta, h.symm (h W.level)), 0)))
      simp only [h.symm_apply_apply]
      have hmap (x : E2) (hx : x ∈ (W.disc b).boundary) :
          G ((heightPlaneCoordinates u).symm (x, W.level)) =
            (heightPlaneCoordinates u).symm (x, h W.level) := by
        have hy : (heightPlaneCoordinates u).symm (x, W.level) ∈
            range (fun theta => psi (W.leg b (theta, W.level), 0)) := by
          rw [← W.disc_boundary b]
          exact ⟨x, hx, rfl⟩
        obtain ⟨theta, htheta⟩ := hy
        let q := W.leg b (theta, W.level)
        change psi (q, 0) = (heightPlaneCoordinates u).symm (x, W.level) at htheta
        have hfq : f q = W.level := by
          change ⟪(u : E3), psi (q, 0)⟫_ℝ = W.level
          rw [← heightPlaneCoordinates_snd u (psi (q, 0)), htheta,
            (heightPlaneCoordinates u).apply_symm_apply]
        have hcoord : heightPlaneCoordinates u (G (psi (q, 0))) =
            ((heightPlaneCoordinates u (psi (q, 0))).1, h (f q)) := by
          apply Prod.ext
          · exact hPlanar _
          · rw [heightPlaneCoordinates_snd, hnew]
        rw [htheta, (heightPlaneCoordinates u).apply_symm_apply, hfq] at hcoord
        apply (heightPlaneCoordinates u).injective
        rw [(heightPlaneCoordinates u).apply_symm_apply]
        exact hcoord
      calc
        _ = (fun x => G ((heightPlaneCoordinates u).symm (x, W.level))) ''
            (W.disc b).boundary := image_congr (fun x hx => (hmap x hx).symm)
        _ = G '' ((fun x => (heightPlaneCoordinates u).symm (x, W.level)) ''
            (W.disc b).boundary) := (image_image _ _ _).symm
        _ = G '' range (fun theta => psi (W.leg b (theta, W.level), 0)) := by
          rw [W.disc_boundary b]
        _ = _ := (range_comp' _ _).symm }

end PoincareConjecture.M25.Topology3D
