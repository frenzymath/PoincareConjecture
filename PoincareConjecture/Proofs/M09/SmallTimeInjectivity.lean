import PoincareConjecture.Proofs.M09.CompactInitialJet
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem eq_zero_of_scaled_equiv_bound (L : E ≃L[ℝ] V) (ε s : ℝ)
    (hε : ‖(L.symm : V →L[ℝ] E)‖ * ε < 1) (hs : 0 < s) (v : E)
    (hv : ‖s • L v‖ ≤ ε * s * ‖v‖) : v = 0 := by
  have hLv : ‖L v‖ ≤ ε * ‖v‖ := by
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      s * ‖L v‖ = ‖s • L v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      _ ≤ ε * s * ‖v‖ := hv
      _ = s * (ε * ‖v‖) := by ring
  have hi : ‖v‖ ≤ ‖(L.symm : V →L[ℝ] E)‖ * ‖L v‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using
      (L.symm : V →L[ℝ] E).le_opNorm (L v)
  have hfinal : ‖v‖ ≤ (‖(L.symm : V →L[ℝ] E)‖ * ε) * ‖v‖ := by
    simpa only [mul_assoc] using hi.trans
      (mul_le_mul_of_nonneg_left hLv (norm_nonneg (L.symm : V →L[ℝ] E)))
  by_contra hv0
  have hp := mul_lt_mul_of_pos_right hε (norm_pos_iff.mpr hv0)
  rw [one_mul] at hp
  exact (not_lt_of_ge hfinal) hp

theorem exists_uniform_smallTime_injective [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    (f : E × ℝ → V) (U : Set (E × ℝ)) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hzeroU : ∀ x, (x, (0 : ℝ)) ∈ U) (q : V) (hzero : ∀ x, f (x, 0) = q)
    (L : E ≃L[ℝ] V) (hjet : ∀ x, HasDerivAt (fun t ↦ f (x, t)) (L x) 0)
    (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, 0 < s → s < δ →
      Set.InjOn (fun x ↦ f (x, s)) K ∧ ∀ x ∈ K,
        (x, s) ∈ U ∧ Function.Bijective (fderiv ℝ (fun y ↦ f (y, s)) x) := by
  let a := ‖(L.symm : V →L[ℝ] E)‖
  let ε := 1 / (2 * (a + 1))
  have ha : 0 ≤ a := norm_nonneg _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsmall : a * ε < 1 := by
    have he : ε * (2 * (a + 1)) = 1 := div_mul_cancel₀ 1 (by positivity)
    nlinarith
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_initialSlice_fderiv_bound f U hU hf
    hzeroU q hzero (L : E →L[ℝ] V) hjet K hK ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ
  have hd (x : E) (hx : x ∈ K) :
      HasFDerivAt (fun y ↦ f (y, s)) (fderiv ℝ (fun y ↦ f (y, s)) x) x :=
    (((hf.contDiffAt (hU.mem_nhds (hbound x hx s hs.le hsδ).1)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasFDerivAt
  have herror (x : E) (hx : x ∈ K) :
      ‖fderiv ℝ (fun y ↦ f (y, s)) x - s • (L : E →L[ℝ] V)‖ ≤ ε * s :=
    (hbound x hx s hs.le hsδ).2
  constructor
  · intro x hx y hy heq
    have hm := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z hz ↦ (hd z hz).hasFDerivWithinAt) herror hx hy
    have hz : y - x = 0 := eq_zero_of_scaled_equiv_bound L ε s hεsmall hs (y - x) (by
      simpa only [heq, sub_self, zero_sub, norm_neg, smul_apply,
        ContinuousLinearEquiv.coe_coe] using hm)
    exact (sub_eq_zero.mp hz).symm
  · intro x hx
    refine ⟨(hbound x hx s hs.le hsδ).1, ?_⟩
    let D := fderiv ℝ (fun y ↦ f (y, s)) x
    have hinj : Function.Injective D := by
      intro v w hvw
      have hzeroD : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
      have hnorm := ((D - s • (L : E →L[ℝ] V)).le_opNorm (v - w)).trans
        (mul_le_mul_of_nonneg_right (herror x hx) (norm_nonneg (v - w)))
      have hz : v - w = 0 := eq_zero_of_scaled_equiv_bound L ε s hεsmall hs (v - w) (by
        simpa only [sub_apply, hzeroD, zero_sub, norm_neg, smul_apply,
          ContinuousLinearEquiv.coe_coe] using hnorm)
      exact sub_eq_zero.mp hz
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := D.toLinearMap) L.toLinearEquiv.finrank_eq).mp hinj⟩

end PoincareConjecture.Proofs.M09
