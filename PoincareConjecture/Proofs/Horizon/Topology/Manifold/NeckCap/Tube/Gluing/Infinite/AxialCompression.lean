import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Vertical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_axial_compression (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p : RoundCylinderSpace, (C p).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ a → C p = p) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ b → (C p).2 < a + δ) ∧
      (∀ q : UnitTwoSphere, StrictMono (fun t : ℝ => (C (q, t)).2)) := by
  let c : ℝ := |b - a| + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let k : ℝ → ℝ := fun t => t + c * Real.smoothTransition ((t - a) / δ)
  have hk : ContDiff ℝ ∞ k := contDiff_id.add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const δ)))
  have hkmono : StrictMono k := by
    intro s t hst
    have hstep := Real.smoothTransition.monotone
      ((div_le_div_iff_of_pos_right hδ).mpr (sub_le_sub_right hst.le a))
    dsimp [k]
    exact add_lt_add_of_lt_of_le hst (mul_le_mul_of_nonneg_left hstep hc.le)
  have hkfixed (t : ℝ) (ht : t ≤ a) : k t = t := by
    simp only [k, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le), mul_zero, add_zero]
  have hksurj : Function.Surjective k := by
    intro y
    have hleft : k (y - c) ≤ y := by
      have hstep := mul_le_mul_of_nonneg_left
        (Real.smoothTransition.le_one ((y - c - a) / δ)) hc.le
      dsimp [k]
      linarith
    have hright : y ≤ k y := by
      exact le_add_of_nonneg_right (mul_nonneg hc.le (Real.smoothTransition.nonneg _))
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (sub_le_self y hc.le)
      hk.continuous.continuousOn ⟨hleft, hright⟩
    exact ⟨t, ht⟩
  have hkderiv (t : ℝ) : HasDerivAt k
      (1 + c * (deriv Real.smoothTransition ((t - a) / δ) / δ)) t := by
    have hs := (((Real.smoothTransition.contDiff :
      ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp))
      ((t - a) / δ)).hasDerivAt
    convert (hasDerivAt_id t).add ((hs.comp t
      (((hasDerivAt_id t).sub_const a).div_const δ)).const_mul c) using 1 <;>
      first | rfl | simp [div_eq_mul_inv]
  have hkpos (t : ℝ) :
      0 < 1 + c * (deriv Real.smoothTransition ((t - a) / δ) / δ) := by
    have hd := Real.smoothTransition.monotone.deriv_nonneg (x := (t - a) / δ)
    positivity
  obtain ⟨D, hD⟩ := exists_vertical_diffeomorph (fun p : RoundCylinderSpace => k p.2)
    (hk.contMDiff.comp contMDiff_snd) (fun _ => ⟨hkmono.injective, hksurj⟩)
    (fun p => ⟨_, (hkpos p.2).ne', hkderiv p.2⟩)
  have hinverse (p : RoundCylinderSpace) :
      (D.symm p).1 = p.1 ∧ k (D.symm p).2 = p.2 := by
    have heq := D.apply_symm_apply p
    rw [hD] at heq
    exact ⟨by simpa only using congrArg Prod.fst heq,
      by simpa only using congrArg Prod.snd heq⟩
  refine ⟨D.symm, fun p => (hinverse p).1, ?_, ?_, ?_⟩
  · intro p hp
    apply D.injective
    change D (D.symm p) = D p
    rw [D.apply_symm_apply, hD, hkfixed p.2 hp]
  · intro p hp
    apply hkmono.lt_iff_lt.mp
    rw [(hinverse p).2]
    have hstep : Real.smoothTransition (((a + δ) - a) / δ) = 1 := by
      rw [add_sub_cancel_left, div_self hδ.ne']
      exact Real.smoothTransition.one
    have hbig : b < k (a + δ) := by
      dsimp [k]
      rw [hstep, mul_one]
      dsimp [c]
      linarith [le_abs_self (b - a)]
    exact hp.trans_lt hbig
  · intro q s t hst
    apply hkmono.lt_iff_lt.mp
    rw [(hinverse (q, s)).2, (hinverse (q, t)).2]
    exact hst

theorem exists_compression_into_open (V : Opens RoundCylinderSpace) (a b : ℝ)
    (hV : ∀ p : RoundCylinderSpace, p.2 ≤ a → p ∈ V) :
    ∃ C : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p : RoundCylinderSpace, (C p).1 = p.1) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ a → C p = p) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ b → C p ∈ V) := by
  let W : Opens RoundCylinderSpace :=
    ⟨{p | (p.1, p.2 + a) ∈ V}, V.isOpen.preimage
      (continuous_fst.prodMk (continuous_snd.add continuous_const))⟩
  have hW (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ W := by
    change (q, 0 + a) ∈ V
    exact hV _ (by simp)
  obtain ⟨δ, hδ, hδW⟩ := exists_cylinder_collar W hW
  obtain ⟨C, hCangle, hCfixed, hCsmall, _⟩ := exists_axial_compression a b hδ
  refine ⟨C, hCangle, hCfixed, ?_⟩
  intro p hp
  by_cases hlow : (C p).2 ≤ a
  · exact hV _ hlow
  · have hnear : |(C p).2 - a| < δ := by
      rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hlow))]
      linarith [hCsmall p hp]
    have hm := hδW ((C p).1, (C p).2 - a) hnear
    change ((C p).1, (C p).2 - a + a) ∈ V at hm
    simpa only [sub_add_cancel, Prod.eta] using hm

end PoincareConjecture.CylinderGluing
