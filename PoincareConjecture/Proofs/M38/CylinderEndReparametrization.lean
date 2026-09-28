import PoincareConjecture.Proofs.M38.UpperEndReparametrization
import PoincareConjecture.Proofs.M38.CylinderEndScaling









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38


noncomputable def cylinderScalarDiffeomorph (e : ℝ ≃o ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ :=
  (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr {
    toEquiv := e.toEquiv
    contMDiff_toFun := he.contMDiff
    contMDiff_invFun := hei.contMDiff }


noncomputable def cylinderEndReflection :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun p := (p.1, 1 - p.2)
  invFun p := (p.1, 1 - p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change 1 - (1 - p.2) = p.2
      ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · change 1 - (1 - p.2) = p.2
      ring
  contMDiff_toFun := contMDiff_fst.prodMk
    ((contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    ((contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_snd)

variable (A : UnitTwoSphere → ℝ) (k : ℝ)
  (hA : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ A) (hk : 0 < k) (hk2 : k ≤ 1 / 2)
  (hAk : ∀ z : UnitTwoSphere, k < A z)


noncomputable def cylinderEndDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ :=
  ((((cylinderScalarDiffeomorph (lowerEndOrderIso k hk hk2)
    (lowerEndProfile_smooth k) (lowerEndOrderIso_symm_smooth hk hk2)).trans
      cylinderEndReflection).trans (cylinderEndScaleDiffeomorph A k hA hk hAk)).trans
        (cylinderScalarDiffeomorph (upperEndOrderIso k hk)
          (upperEndProfile_smooth k) (upperEndOrderIso_symm_smooth hk))).trans
            cylinderEndReflection


theorem cylinderEndDiffeomorph_apply (p : RoundCylinderSpace) :
    cylinderEndDiffeomorph A k hA hk hk2 hAk p =
      (p.1, 1 - upperEndProfile k
        (endScaleProfile (k / A p.1) (1 - lowerEndProfile k p.2))) := rfl


theorem cylinderEndDiffeomorph_symm_apply (p : RoundCylinderSpace) :
    (cylinderEndDiffeomorph A k hA hk hk2 hAk).symm p =
      (p.1, (lowerEndOrderIso k hk hk2).symm
        (1 - endScaleInverse (k / A p.1) ((upperEndOrderIso k hk).symm (1 - p.2)))) := rfl


theorem cylinderEndDiffeomorph_zero (z : UnitTwoSphere) :
    cylinderEndDiffeomorph A k hA hk hk2 hAk (z, 0) = (z, 0) := by
  rw [cylinderEndDiffeomorph_apply]
  have hl : lowerEndProfile k 0 = 0 := lowerEndOrderIso_zero k hk hk2
  have hu : upperEndProfile k 1 = 1 := upperEndOrderIso_one k hk
  simp only [hl, sub_zero, endScaleProfile_one, hu, sub_self]


theorem cylinderEndDiffeomorph_one (z : UnitTwoSphere) :
    cylinderEndDiffeomorph A k hA hk hk2 hAk (z, 1) = (z, 1) := by
  rw [cylinderEndDiffeomorph_apply]
  have hl : lowerEndProfile k 1 = 1 := lowerEndOrderIso_one k hk hk2
  have hu : upperEndProfile k 0 = 0 := upperEndOrderIso_zero k hk
  simp only [hl, sub_self, endScaleProfile_zero, hu, sub_zero]


theorem cylinderEndDiffeomorph_strictMono (z : UnitTwoSphere) :
    StrictMono (fun t : ℝ => (cylinderEndDiffeomorph A k hA hk hk2 hAk (z, t)).2) := by
  intro s t hst
  change 1 - upperEndProfile k (endScaleProfile (k / A z) (1 - lowerEndProfile k s)) <
    1 - upperEndProfile k (endScaleProfile (k / A z) (1 - lowerEndProfile k t))
  apply sub_lt_sub_left _ 1
  apply upperEndProfile_strictMono hk
  apply endScaleProfile_strictMono
    (cylinderEndScale_coefficient A k hk hAk z).1
    (cylinderEndScale_coefficient A k hk hAk z).2
  exact sub_lt_sub_left (lowerEndProfile_strictMono hk hk2 hst) 1


theorem cylinderEndDiffeomorph_mem_iff (p : RoundCylinderSpace) :
    cylinderEndDiffeomorph A k hA hk hk2 hAk p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 ↔
      p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := by
  have hmono := cylinderEndDiffeomorph_strictMono A k hA hk hk2 hAk p.1
  have hzero := congrArg Prod.snd (cylinderEndDiffeomorph_zero A k hA hk hk2 hAk p.1)
  have hone := congrArg Prod.snd (cylinderEndDiffeomorph_one A k hA hk hk2 hAk p.1)
  constructor
  · intro hp
    refine ⟨Set.mem_univ _, hmono.lt_iff_lt.mp ?_, hmono.lt_iff_lt.mp ?_⟩
    · simpa only [hzero] using hp.2.1
    · simpa only [hone] using hp.2.2
  · intro hp
    refine ⟨Set.mem_univ _, ?_, ?_⟩
    · simpa only [hzero] using hmono hp.2.1
    · simpa only [hone] using hmono hp.2.2


theorem cylinderEndDiffeomorph_image_strip :
    cylinderEndDiffeomorph A k hA hk hk2 hAk '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) =
      Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    exact (cylinderEndDiffeomorph_mem_iff A k hA hk hk2 hAk p).mpr hp
  · intro y hy
    refine ⟨(cylinderEndDiffeomorph A k hA hk hk2 hAk).symm y, ?_,
      (cylinderEndDiffeomorph A k hA hk hk2 hAk).apply_symm_apply y⟩
    apply (cylinderEndDiffeomorph_mem_iff A k hA hk hk2 hAk _).mp
    rw [(cylinderEndDiffeomorph A k hA hk hk2 hAk).apply_symm_apply]
    exact hy


theorem cylinderEndDiffeomorph_lower (z : UnitTwoSphere) {s : ℝ}
    (hs : 0 < s) (hs8 : s ≤ 1 / 8) :
    cylinderEndDiffeomorph A k hA hk hk2 hAk (z, s / (1 + s)) = (z, k * s) := by
  have hden : 0 < 1 + s := by linarith
  have hy0 : 0 ≤ s / (1 + s) := (div_pos hs hden).le
  have hy8 : |s / (1 + s)| ≤ 1 / 8 := by
    rw [abs_of_nonneg hy0]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hrational : k * (s / (1 + s)) / (1 - s / (1 + s)) = k * s := by
    field_simp [hden.ne']
    ring
  have hks : k * s ≤ 1 / 16 := by nlinarith
  rw [cylinderEndDiffeomorph_apply, lowerEndProfile_inner k hy8, hrational,
    endScaleProfile_outer (k / A z) (by linarith), upperEndProfile_outer k (by linarith)]
  congr 1
  ring



theorem cylinderEndDiffeomorph_upper (z : UnitTwoSphere) {s : ℝ}
    (hsource : A z * punctureRadialOrderIso (1 + s) ≤ 5 / 32)
    (htarget : k * punctureRadialOrderIso (1 + s) ≤ 1 / 8) :
    cylinderEndDiffeomorph A k hA hk hk2 hAk
      (z, 1 - A z * punctureRadialOrderIso (1 + s)) = (z, 1 - k * s) := by
  have hy : 1 / 4 ≤ |1 - A z * punctureRadialOrderIso (1 + s)| :=
    (show 1 / 4 ≤ 1 - A z * punctureRadialOrderIso (1 + s) by linarith).trans
      (le_abs_self _)
  have hcancel : (k / A z) * (A z * punctureRadialOrderIso (1 + s)) =
      k * punctureRadialOrderIso (1 + s) := by field_simp [(hk.trans (hAk z)).ne']
  rw [cylinderEndDiffeomorph_apply, lowerEndProfile_outer k hy, sub_sub_cancel,
    endScaleProfile_inner (k / A z) hsource, hcancel, upperEndProfile_inner k htarget]
  change (z, 1 - k * (punctureRadialOrderIso.symm
    ((k * punctureRadialOrderIso (1 + s)) / k) - 1)) = (z, 1 - k * s)
  rw [mul_div_cancel_left₀ _ hk.ne', OrderIso.symm_apply_apply]
  congr 1
  ring

end PoincareConjecture.M38
