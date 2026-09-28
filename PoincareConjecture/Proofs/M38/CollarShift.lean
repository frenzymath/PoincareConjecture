import PoincareConjecture.Proofs.M38.CollarMotion
import PoincareConjecture.Proofs.M38.LowerEndReparametrization









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38



theorem exists_supported_negative_shift {R : ℝ} (hR : 0 < R) :
    ∃ e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      StrictMono e ∧ e 0 < 0 ∧ -R < e 0 ∧
      ∀ s : ℝ, R ≤ |s| → e s = s := by
  let L : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toFun := fun s => s / R + 1 / 16
    invFun := fun s => R * (s - 1 / 16)
    left_inv := by
      intro s
      dsimp
      field_simp
      ring
    right_inv := by
      intro s
      dsimp
      field_simp
      ring
    contMDiff_toFun := ((contDiff_id.div_const R).add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff }
  let l := lowerEndOrderIso (1 / 4) (by norm_num) (by norm_num)
  let D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := l.toEquiv
    contMDiff_toFun := (lowerEndProfile_smooth (1 / 4)).contMDiff
    contMDiff_invFun := (lowerEndOrderIso_symm_smooth (by norm_num : 0 < (1 : ℝ) / 4)
      (by norm_num)).contMDiff }
  let e := (L.trans D).trans L.symm
  have hformula (s : ℝ) : e s =
      R * (lowerEndProfile (1 / 4) (s / R + 1 / 16) - 1 / 16) := rfl
  have he0 : e 0 = -(11 / 240) * R := by
    rw [hformula]
    simp only [zero_div, zero_add]
    rw [lowerEndProfile_inner (1 / 4) (by norm_num : |(1 : ℝ) / 16| ≤ 1 / 8)]
    ring
  refine ⟨e, ?_, by rw [he0]; linarith, by rw [he0]; linarith, ?_⟩
  · intro s t hst
    rw [hformula, hformula]
    apply mul_lt_mul_of_pos_left _ hR
    apply sub_lt_sub_right
    exact lowerEndProfile_strictMono (by norm_num) (by norm_num)
      (by linarith [div_lt_div_of_pos_right hst hR])
  · intro s hs
    have hout : 1 / 4 ≤ |s / R + 1 / 16| := by
      by_contra h
      have hh := abs_lt.mp (lt_of_not_ge h)
      have hlo : -R < s := by
        simpa using (lt_div_iff₀ hR).mp (by linarith : -1 < s / R)
      have hhi : s < R := by
        simpa using (div_lt_iff₀ hR).mp (by linarith : s / R < 1)
      exact (not_lt_of_ge hs) (abs_lt.mpr ⟨hlo, hhi⟩)
    rw [hformula, lowerEndProfile_outer (1 / 4) hout]
    field_simp
    ring



theorem exists_negative_collar_motion
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace StandardCapSpace Q] [T2Space Q]
    (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace Q ∞)
    {δ R : ℝ} (hR : 0 < R) (hRδ : R < δ)
    (hc : c.source = univ ×ˢ Ioo (-δ) δ) :
    ∃ (e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (H : Diffeomorph (𝓡 3) (𝓡 3) Q Q ∞),
      StrictMono e ∧ e 0 < 0 ∧ -R < e 0 ∧
      (∀ s : ℝ, R ≤ |s| → e s = s) ∧
      (∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-δ) δ →
        H (c (z, s)) = c (z, e s)) ∧
      ∀ x : Q, x ∉ c '' (univ ×ˢ Icc (-R) R) → H x = x := by
  obtain ⟨e, he, he0, heR, hfix⟩ := exists_supported_negative_shift hR
  obtain ⟨H, hH, hHfix⟩ := exists_ambient_collar_motion c hRδ hc e hfix
  exact ⟨e, H, he, he0, heR, hfix, hH, hHfix⟩

end PoincareConjecture.M38
