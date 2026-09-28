import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.AxialShift
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_variable_axial_expansion (a δ d : UnitTwoSphere → ℝ)
    (ha : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ a)
    (hδ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ δ)
    (hd : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ d)
    (hδpos : ∀ q, 0 < δ q) (hdnonneg : ∀ q, 0 ≤ d q) :
    ∃ D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p : RoundCylinderSpace,
        D p = (p.1, p.2 + d p.1 * Real.smoothTransition ((p.2 - a p.1) / δ p.1))) ∧
      (∀ q : UnitTwoSphere, StrictMono (fun t : ℝ => (D (q, t)).2)) := by
  let k : RoundCylinderSpace → ℝ :=
    fun p => p.2 + d p.1 * Real.smoothTransition ((p.2 - a p.1) / δ p.1)
  have hk : ContMDiff CylModel 𝓘(ℝ, ℝ) ∞ k :=
    contMDiff_snd.add ((hd.comp contMDiff_fst).mul
      (Real.smoothTransition.contDiff.contMDiff.comp
        ((contMDiff_snd.sub (ha.comp contMDiff_fst)).div₀
          (hδ.comp contMDiff_fst) (fun p => (hδpos p.1).ne'))))
  have hkmono (q : UnitTwoSphere) : StrictMono (fun t => k (q, t)) := by
    intro s t hst
    have hstep := Real.smoothTransition.monotone
      ((div_le_div_iff_of_pos_right (hδpos q)).mpr (sub_le_sub_right hst.le (a q)))
    exact add_lt_add_of_lt_of_le hst (mul_le_mul_of_nonneg_left hstep (hdnonneg q))
  have hksurj (q : UnitTwoSphere) : Function.Surjective (fun t => k (q, t)) := by
    intro y
    have hleft : k (q, y - d q) ≤ y := by
      have hstep := mul_le_mul_of_nonneg_left
        (Real.smoothTransition.le_one ((y - d q - a q) / δ q)) (hdnonneg q)
      dsimp [k]
      linarith
    have hright : y ≤ k (q, y) :=
      le_add_of_nonneg_right (mul_nonneg (hdnonneg q) (Real.smoothTransition.nonneg _))
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (sub_le_self y (hdnonneg q))
      (hk.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn ⟨hleft, hright⟩
    exact ⟨t, ht⟩
  have hkderiv (q : UnitTwoSphere) (t : ℝ) : HasDerivAt (fun s => k (q, s))
      (1 + d q * (deriv Real.smoothTransition ((t - a q) / δ q) / δ q)) t := by
    have hs := (((Real.smoothTransition.contDiff :
      ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp))
      ((t - a q) / δ q)).hasDerivAt
    convert (hasDerivAt_id t).add ((hs.comp t
      (((hasDerivAt_id t).sub_const (a q)).div_const (δ q))).const_mul (d q)) using 1 <;>
      first | rfl | simp [div_eq_mul_inv]
  have hkpos (q : UnitTwoSphere) (t : ℝ) :
      0 < 1 + d q * (deriv Real.smoothTransition ((t - a q) / δ q) / δ q) := by
    have hnonneg := Real.smoothTransition.monotone.deriv_nonneg (x := (t - a q) / δ q)
    have hδq := hδpos q
    have hdq := hdnonneg q
    positivity
  obtain ⟨D, hD⟩ := exists_vertical_diffeomorph k hk
    (fun q => ⟨(hkmono q).injective, hksurj q⟩)
    (fun p => ⟨_, (hkpos p.1 p.2).ne', hkderiv p.1 p.2⟩)
  refine ⟨D, hD, ?_⟩
  intro q s t hst
  simpa only [hD] using hkmono q hst

theorem exists_supported_graph_shift {l b r : ℝ} (hlb : l < b)
    (h : UnitTwoSphere → ℝ) (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hlo : ∀ q, b < h q) (hhi : ∀ q, h q < r) :
    ∃ D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p : RoundCylinderSpace, (D p).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ l ∨ r ≤ p.2 → D p = p) ∧
      (∀ q : UnitTwoSphere, D (q, b) = (q, h q)) := by
  let δL := (b - l) / 2
  let aR : UnitTwoSphere → ℝ := fun q => (h q + r) / 2
  let δR : UnitTwoSphere → ℝ := fun q => (r - h q) / 2
  let d : UnitTwoSphere → ℝ := fun q => h q - b
  have hδL : 0 < δL := by dsimp [δL]; linarith
  have hδR (q : UnitTwoSphere) : 0 < δR q := by dsimp [δR]; linarith [hhi q]
  have hd : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ d := hh.sub contMDiff_const
  obtain ⟨L, hL, _⟩ := exists_variable_axial_expansion (fun _ => l) (fun _ => δL) d
    contMDiff_const contMDiff_const hd (fun _ => hδL) (fun q => (sub_pos.mpr (hlo q)).le)
  obtain ⟨R, hR, _⟩ := exists_variable_axial_expansion aR δR d
    ((hh.add contMDiff_const).div_const 2) ((contMDiff_const.sub hh).div_const 2)
    hd hδR (fun q => (sub_pos.mpr (hlo q)).le)
  have hLlow (p : RoundCylinderSpace) (hp : p.2 ≤ l) : L p = p := by
    rw [hL, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) hδL.le)]
    simp only [mul_zero, add_zero, Prod.eta]
  have hRlow (p : RoundCylinderSpace) (hp : p.2 ≤ aR p.1) : R p = p := by
    rw [hR, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (hδR p.1).le)]
    simp only [mul_zero, add_zero, Prod.eta]
  have hLhigh (p : RoundCylinderSpace) (hp : l + δL ≤ p.2) :
      L p = (p.1, p.2 + d p.1) := by
    rw [hL, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδL).mpr (by linarith)), mul_one]
  have hRhigh (p : RoundCylinderSpace) (hp : r ≤ p.2) :
      R p = (p.1, p.2 + d p.1) := by
    rw [hR, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ (hδR p.1)).mpr (by dsimp [δR, aR]; linarith)), mul_one]
  have hRinvfst (p : RoundCylinderSpace) : (R.symm p).1 = p.1 := by
    have hRp := R.apply_symm_apply p
    rw [hR] at hRp
    simpa only using congrArg Prod.fst hRp
  refine ⟨L.trans R.symm, ?_, ?_, ?_⟩
  · intro p
    change (R.symm (L p)).1 = p.1
    rw [hRinvfst, hL]
  · intro p hp
    change R.symm (L p) = p
    apply R.injective
    change R (R.symm (L p)) = R p
    rw [R.apply_symm_apply]
    rcases hp with hp | hp
    · rw [hLlow p hp, hRlow p (by dsimp [aR]; linarith [hlo p.1, hhi p.1])]
    · rw [hLhigh p (by dsimp [δL]; linarith [hlo p.1, hhi p.1]), hRhigh p hp]
  · intro q
    change R.symm (L (q, b)) = (q, h q)
    apply R.injective
    change R (R.symm (L (q, b))) = R (q, h q)
    rw [R.apply_symm_apply, hLhigh _ (by dsimp [δL]; linarith),
      hRlow _ (by dsimp [aR]; linarith [hhi q])]
    dsimp [d]
    congr 1
    ring

end PoincareConjecture.CylinderGluing
