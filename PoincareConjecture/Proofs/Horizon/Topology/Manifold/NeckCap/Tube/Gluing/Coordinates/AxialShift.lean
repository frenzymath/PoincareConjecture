import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Vertical
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


theorem exists_axial_expansion (a : ℝ) {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d) :
    ∃ D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p : RoundCylinderSpace,
        D p = (p.1, p.2 + d * Real.smoothTransition ((p.2 - a) / δ))) ∧
      (∀ q : UnitTwoSphere, StrictMono (fun t : ℝ => (D (q, t)).2)) := by
  let k : ℝ → ℝ := fun t => t + d * Real.smoothTransition ((t - a) / δ)
  have hk : ContDiff ℝ ∞ k := contDiff_id.add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const δ)))
  have hkmono : StrictMono k := by
    intro s t hst
    have hstep := Real.smoothTransition.monotone
      ((div_le_div_iff_of_pos_right hδ).mpr (sub_le_sub_right hst.le a))
    exact add_lt_add_of_lt_of_le hst (mul_le_mul_of_nonneg_left hstep hd)
  have hksurj : Function.Surjective k := by
    intro y
    have hleft : k (y - d) ≤ y := by
      have hstep := mul_le_mul_of_nonneg_left
        (Real.smoothTransition.le_one ((y - d - a) / δ)) hd
      dsimp [k]
      linarith
    have hright : y ≤ k y :=
      le_add_of_nonneg_right (mul_nonneg hd (Real.smoothTransition.nonneg _))
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (sub_le_self y hd)
      hk.continuous.continuousOn ⟨hleft, hright⟩
    exact ⟨t, ht⟩
  have hkderiv (t : ℝ) : HasDerivAt k
      (1 + d * (deriv Real.smoothTransition ((t - a) / δ) / δ)) t := by
    have hs := (((Real.smoothTransition.contDiff :
      ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp))
      ((t - a) / δ)).hasDerivAt
    convert (hasDerivAt_id t).add ((hs.comp t
      (((hasDerivAt_id t).sub_const a).div_const δ)).const_mul d) using 1 <;>
      first | rfl | simp [div_eq_mul_inv]
  have hkpos (t : ℝ) :
      0 < 1 + d * (deriv Real.smoothTransition ((t - a) / δ) / δ) := by
    have hnonneg := Real.smoothTransition.monotone.deriv_nonneg (x := (t - a) / δ)
    positivity
  obtain ⟨D, hD⟩ := exists_vertical_diffeomorph (fun p : RoundCylinderSpace => k p.2)
    (hk.contMDiff.comp contMDiff_snd) (fun _ => ⟨hkmono.injective, hksurj⟩)
    (fun p => ⟨_, (hkpos p.2).ne', hkderiv p.2⟩)
  refine ⟨D, hD, ?_⟩
  intro q s t hst
  simpa only [hD] using hkmono hst



theorem exists_supported_axial_shift {l b c r : ℝ}
    (hlb : l < b) (hbc : b < c) (hcr : c < r) :
    ∃ (ρ : ℝ) (D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
      0 < ρ ∧
      (∀ p : RoundCylinderSpace, (D p).1 = p.1) ∧
      (∀ q : UnitTwoSphere, StrictMono (fun t : ℝ => (D (q, t)).2)) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ l ∨ r ≤ p.2 → D p = p) ∧
      (∀ p : RoundCylinderSpace, |p.2 - b| < ρ → D p = (p.1, p.2 + (c - b))) := by
  let δL := (b - l) / 2
  let aR := (c + r) / 2
  let δR := (r - c) / 2
  have hδL : 0 < δL := by dsimp [δL]; linarith
  have hδR : 0 < δR := by dsimp [δR]; linarith
  have hcR : c < aR := by dsimp [aR]; linarith
  obtain ⟨L, hL, hLmono⟩ := exists_axial_expansion l hδL (sub_pos.mpr hbc).le
  obtain ⟨R, hR, hRmono⟩ := exists_axial_expansion aR hδR (sub_pos.mpr hbc).le
  have hLlow (p : RoundCylinderSpace) (hp : p.2 ≤ l) : L p = p := by
    rw [hL, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) hδL.le)]
    simp only [mul_zero, add_zero, Prod.eta]
  have hRlow (p : RoundCylinderSpace) (hp : p.2 ≤ aR) : R p = p := by
    rw [hR, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) hδR.le)]
    simp only [mul_zero, add_zero, Prod.eta]
  have hLhigh (p : RoundCylinderSpace) (hp : l + δL ≤ p.2) :
      L p = (p.1, p.2 + (c - b)) := by
    rw [hL, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδL).mpr (by linarith)), mul_one]
  have hRhigh (p : RoundCylinderSpace) (hp : r ≤ p.2) :
      R p = (p.1, p.2 + (c - b)) := by
    rw [hR, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδR).mpr (by dsimp [δR, aR]; linarith)), mul_one]
  have hRinvfst (p : RoundCylinderSpace) : (R.symm p).1 = p.1 := by
    have h := R.apply_symm_apply p
    rw [hR] at h
    simpa only using congrArg Prod.fst h
  have hRinvmono (q : UnitTwoSphere) : StrictMono (fun t : ℝ => (R.symm (q, t)).2) := by
    intro s t hst
    apply (hRmono q).lt_iff_lt.mp
    have hs : R (q, (R.symm (q, s)).2) = (q, s) := by
      rw [show (q, (R.symm (q, s)).2) = R.symm (q, s) from
        Prod.ext (hRinvfst (q, s)).symm rfl, R.apply_symm_apply]
    have ht : R (q, (R.symm (q, t)).2) = (q, t) := by
      rw [show (q, (R.symm (q, t)).2) = R.symm (q, t) from
        Prod.ext (hRinvfst (q, t)).symm rfl, R.apply_symm_apply]
    simpa only [hs, ht] using hst
  let ρ := min δL δR
  have hρ : 0 < ρ := lt_min hδL hδR
  refine ⟨ρ, L.trans R.symm, hρ, ?_, ?_, ?_, ?_⟩
  · intro p
    change (R.symm (L p)).1 = p.1
    rw [hRinvfst, hL]
  · intro q s t hst
    have hs := hRinvmono q ((hLmono q) hst)
    change (R.symm (L (q, s))).2 < (R.symm (L (q, t))).2
    simpa only [hL] using hs
  · intro p hp
    change R.symm (L p) = p
    apply R.injective
    change R (R.symm (L p)) = R p
    rw [R.apply_symm_apply]
    rcases hp with hp | hp
    · rw [hLlow p hp, hRlow p (hp.trans (by linarith))]
    · rw [hLhigh p (by dsimp [δL]; linarith), hRhigh p hp]
  · intro p hp
    have hlo := (abs_lt.mp hp).1
    have hhi := (abs_lt.mp hp).2
    have hρL : ρ ≤ δL := min_le_left _ _
    have hρR : ρ ≤ δR := min_le_right _ _
    change R.symm (L p) = (p.1, p.2 + (c - b))
    apply R.injective
    change R (R.symm (L p)) = R (p.1, p.2 + (c - b))
    rw [R.apply_symm_apply, hLhigh p (by dsimp [δL] at *; linarith),
      hRlow _ (by dsimp [aR, δR] at *; linarith)]

end PoincareConjecture.CylinderGluing
