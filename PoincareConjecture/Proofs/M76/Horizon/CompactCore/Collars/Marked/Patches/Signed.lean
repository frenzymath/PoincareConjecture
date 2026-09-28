import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Patches.Extension
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Patches.Orientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.SignedPatches



set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)

theorem exists_partial_signed_patches
    {a b w : ℝ} (ha : -(1 / 2 : ℝ) < a) (hab : a < b) (hb : b < 3 / 2)
    (hw : 0 < w) (hwsmall : w ≤ 1 / 2)
    {g : P2 → P2} (hg : FinitePiecewiseAffineOn g (Icc (-w) w ×ˢ Icc a b))
    (hi : InjOn g (Icc (-w) w ×ˢ Icc a b))
    (hmap : MapsTo g (Icc (-w) w ×ˢ Icc a b)
      (Ioo (-(1 / 2 : ℝ)) (3 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hcenter : ∀ t ∈ Icc a b, g (0, t) = (t, 0))
    (hzero : ∀ p ∈ Icc (-w) w ×ˢ Icc a b, (g p).2 = 0 ↔ p.1 = 0) :
    ∃ (o : Bool) (H : Bool → halfArmRectangle ≃ₜ halfArmRectangle),
      (∀ side, (H side).IsFinitePL) ∧
      (∀ side (p : halfArmRectangle), (p : P2) ∈ frontier halfArmRectangle → H side p = p) ∧
      ∀ side p (hp : p ∈ Icc a b ×ˢ Icc 0 (w / 2)),
        (H side ⟨p, by
          exact ⟨⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩,
            hp.2.1, by linarith [hp.2.2]⟩⟩ : P2) =
          halfPatchOutput side (g (sign o * (sign side * p.2), p.1)) := by
  classical
  obtain ⟨o, hpos, hneg⟩ := exists_partial_planar_strip_orientation hw hab hg hi hcenter hzero
  have hbuild (side : Bool) :
      ∃ H : halfArmRectangle ≃ₜ halfArmRectangle, H.IsFinitePL ∧
        (∀ p (hp : p ∈ Icc a b ×ˢ Icc 0 (w / 2)),
          (H ⟨p, by
            exact ⟨⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩,
              hp.2.1, by linarith [hp.2.2]⟩⟩ : P2) =
            halfPatchOutput side (g (sign o * (sign side * p.2), p.1))) ∧
        ∀ p : halfArmRectangle, (p : P2) ∈ frontier halfArmRectangle → H p = p := by
    let A := (stripReflection o).comp (halfPatchInput side)
    have hAvalue (p : P2) : A p = (sign o * (sign side * p.2), p.1) := rfl
    have hAi : Function.Injective A := by
      intro p q hpq
      cases o <;> cases side <;> simpa [A, sign, Prod.ext_iff, and_comm] using hpq
    have hinput : MapsTo A (Icc a b ×ˢ Icc 0 (w / 2)) (Icc (-w) w ×ˢ Icc a b) := by
      intro p hp
      refine ⟨?_, hp.1⟩
      cases o <;> cases side <;> simp only [hAvalue, sign, Bool.false_eq_true, if_false,
        if_true, one_mul, neg_one_mul, neg_neg, mem_Icc]
      all_goals constructor <;> linarith [hp.2.1, hp.2.2]
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      (isFinitePLBallPair_Icc hab).prod (isFinitePLBallPair_Icc (half_pos hw))
    have hAPL : FinitePiecewiseAffineOn A (Icc a b ×ˢ Icc 0 (w / 2)) :=
      ⟨K, hK, hKs, K.affineOnFaces_affine A⟩
    let G := halfPatchOutput side ∘ g ∘ A
    have hG : FinitePiecewiseAffineOn G (Icc a b ×ˢ Icc 0 (w / 2)) :=
      (hg.comp hAPL hinput).postcomp (halfPatchOutput side)
    have hout : Function.Injective (halfPatchOutput side) := by
      intro p q hpq
      cases side <;> simpa [sign, Prod.ext_iff] using hpq
    have hGi : InjOn G (Icc a b ×ˢ Icc 0 (w / 2)) :=
      fun p hp q hq heq => hAi (hi (hinput hp) (hinput hq) (hout heq))
    apply exists_partial_half_arm_patch_extension ha hab hb (half_pos hw) (by linarith) hG hGi
    · intro p hp
      have hm := hmap (hinput hp)
      refine ⟨hm.1, ?_, ?_⟩
      · by_cases hz : p.2 = 0
        · have hgz : (g (A p)).2 = 0 := (hzero _ (hinput hp)).mpr (by simp [hAvalue, hz])
          change 0 ≤ sign side * (g (A p)).2
          rw [hgz, mul_zero]
        · have hp0 : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hz)
          cases o <;> cases side
          · have hh := hpos (p.2, p.1) ⟨⟨hp0, by linarith [hp.2.2]⟩, hp.1⟩
            simpa [G, A, sign] using hh.le
          · have hh := hneg (-p.2, p.1) ⟨⟨by linarith [hp.2.2], by linarith⟩, hp.1⟩
            simpa [G, A, sign] using (neg_nonneg.mpr hh.le)
          · have hh := hneg (-p.2, p.1) ⟨⟨by linarith [hp.2.2], by linarith⟩, hp.1⟩
            simpa [G, A, sign] using (neg_nonneg.mpr hh.le)
          · have hh := hpos (p.2, p.1) ⟨⟨hp0, by linarith [hp.2.2]⟩, hp.1⟩
            simpa [G, A, sign] using hh.le
      · cases side
        · simpa [G, sign] using hm.2.2
        · simpa [G, sign] using (neg_lt_neg hm.2.1)
    · intro t ht
      simp only [G, Function.comp_apply, hAvalue, mul_zero, hcenter t ht,
        halfPatchOutput_apply]
    · intro p hp
      have hh := hzero (A p) (hinput hp)
      cases o <;> cases side <;> simpa [G, hAvalue, sign] using hh
  choose H hH hvalue hfixed using hbuild
  exact ⟨o, H, hH, hfixed, hvalue⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
