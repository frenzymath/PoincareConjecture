import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.QuadraticFactor
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Diffeomorphism.LocalInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt









noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus.Morse


def rescalingShearMap (u v w : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (u x * (x.1 + v x * x.2), w x * x.2)


def rescalingShearLinear (u v w : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (u • (ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (w • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp]
theorem rescalingShearLinear_apply (u v w : ℝ) (x : ℝ × ℝ) :
    rescalingShearLinear u v w x = (u * (x.1 + v * x.2), w * x.2) := rfl

theorem hasFDerivAt_rescalingShearMap_zero {u v w : ℝ × ℝ → ℝ}
    (hu : DifferentiableAt ℝ u 0) (hv : DifferentiableAt ℝ v 0)
    (hw : DifferentiableAt ℝ w 0) :
    HasFDerivAt (rescalingShearMap u v w)
      (rescalingShearLinear (u 0) (v 0) (w 0)) 0 := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (0, 0))
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (0, 0))
  convert! (hu.hasFDerivAt.mul (hx.add (hv.hasFDerivAt.mul hy))).prodMk
    (hw.hasFDerivAt.mul hy) using 1
  ext <;> simp [rescalingShearLinear]

theorem bijective_rescalingShearLinear {u v w : ℝ} (hu : u ≠ 0) (hw : w ≠ 0) :
    Function.Bijective (rescalingShearLinear u v w) := by
  constructor
  · intro x y h
    have hsecond := congrArg Prod.snd h
    have hfirst := congrArg Prod.fst h
    simp only [rescalingShearLinear_apply] at hfirst hsecond
    have hxy : x.2 = y.2 := (mul_left_cancel₀ hw hsecond)
    apply Prod.ext
    · rw [hxy] at hfirst
      exact add_right_cancel (mul_left_cancel₀ hu hfirst)
    · exact hxy
  · intro y
    refine ⟨(y.1 / u - v * (y.2 / w), y.2 / w), ?_⟩
    ext <;> simp only [rescalingShearLinear_apply]
    · field_simp
      ring
    · exact mul_div_cancel₀ _ hw



theorem exists_rescalingShear_localInverse {u v w : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h0 : (0 : ℝ × ℝ) ∈ U)
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hw : ContDiffOn ℝ ∞ w U) (hu0 : u 0 ≠ 0) (hw0 : w 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (0 : ℝ × ℝ) ∈ e.source ∧ e 0 = 0 ∧ e.source ⊆ U ∧
      (e : (ℝ × ℝ) → ℝ × ℝ) = rescalingShearMap u v w ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let g := rescalingShearMap u v w
  have hg : ContDiffOn ℝ ∞ g U :=
    (hu.mul (contDiff_fst.contDiffOn.add (hv.mul contDiff_snd.contDiffOn))).prodMk
      (hw.mul contDiff_snd.contDiffOn)
  have hg0 : ContDiffAt ℝ ∞ g 0 := hg.contDiffAt (hU.mem_nhds h0)
  let A := ContinuousLinearEquiv.ofBijective
    (rescalingShearLinear (u 0) (v 0) (w 0))
    (LinearMap.ker_eq_bot.mpr (bijective_rescalingShearLinear hu0 hw0).1)
    (LinearMap.range_eq_top.mpr (bijective_rescalingShearLinear hu0 hw0).2)
  have hd : HasFDerivAt g (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) 0 := by
    convert! hasFDerivAt_rescalingShearMap_zero
      ((hu.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp))
      ((hv.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp))
      ((hw.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)) using 1
  let Q := hg0.toOpenPartialHomeomorph g hd (by simp)
  let N : Set (ℝ × ℝ) := U ∩ (fderiv ℝ g) ⁻¹'
    range ((↑) : ((ℝ × ℝ) ≃L[ℝ] ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ × ℝ)
  have hN : IsOpen N :=
    (hg.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen
  have h0N : (0 : ℝ × ℝ) ∈ N := ⟨h0, A, hd.fderiv.symm⟩
  let e := Q.restrOpen N hN
  have hes : e.source ⊆ U := fun _ hx => hx.2.1
  refine ⟨e, ⟨hg0.mem_toOpenPartialHomeomorph_source hd (by simp), h0N⟩,
    ?_, hes, rfl, hg.mono hes, ?_⟩
  · change rescalingShearMap u v w 0 = 0
    simp [rescalingShearMap]
  · intro y hy
    have hx := e.map_target hy
    obtain ⟨C, hC⟩ := hx.2.2
    have hgat := hg.contDiffAt (hU.mem_nhds (hes hx))
    apply (e.contDiffAt_symm hy (f₀' := C) ?_ hgat).contDiffWithinAt
    rw [hC]
    exact (hgat.differentiableAt (by simp)).hasFDerivAt


theorem binary_quadratic_complete_square {a b c x y : ℝ} (ha : a ≠ 0) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 =
      a * (x + b / a * y) ^ 2 + (c - b ^ 2 / a) * y ^ 2 := by
  field_simp
  ring


theorem binary_quadratic_signed_squares {a b c x y s t : ℝ}
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (ha : 0 < s * a) (hc : 0 < t * (c - b ^ 2 / a)) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 =
      s * (Real.sqrt (s * a) * (x + b / a * y)) ^ 2 +
      t * (Real.sqrt (t * (c - b ^ 2 / a)) * y) ^ 2 := by
  have hane : a ≠ 0 := by intro h; simp [h] at ha
  rw [binary_quadratic_complete_square hane]
  rw [mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hc.le]
  calc
    _ = s ^ 2 * a * (x + b / a * y) ^ 2 + t ^ 2 * (c - b ^ 2 / a) * y ^ 2 := by
      rw [hs, ht]
      ring
    _ = _ := by ring

private theorem exists_sign_mul_pos {a : ℝ} (ha : a ≠ 0) :
    ∃ s : ℝ, (s = -1 ∨ s = 1) ∧ s ^ 2 = 1 ∧ 0 < s * a := by
  rcases lt_or_gt_of_ne ha with h | h
  · exact ⟨-1, Or.inl rfl, by norm_num, by nlinarith⟩
  · exact ⟨1, Or.inr rfl, by norm_num, by simpa⟩



theorem exists_binary_quadratic_normalForm
    {a b c : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
    (ha0 : a 0 ≠ 0) (hd0 : c 0 - b 0 ^ 2 / a 0 ≠ 0) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (s t : ℝ),
      (s = -1 ∨ s = 1) ∧ (t = -1 ∨ t = 1) ∧
      (0 : ℝ × ℝ) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source,
        a (e x) * (e x).1 ^ 2 + 2 * b (e x) * (e x).1 * (e x).2 +
          c (e x) * (e x).2 ^ 2 = s * x.1 ^ 2 + t * x.2 ^ 2 := by
  obtain ⟨s, hs, hs2, hsa⟩ := exists_sign_mul_pos ha0
  obtain ⟨t, ht, ht2, htd⟩ := exists_sign_mul_pos hd0
  let d : ℝ × ℝ → ℝ := fun x => c x - b x ^ 2 / a x
  let W : Set (ℝ × ℝ) := (fun x => s * a x) ⁻¹' Ioi 0
  have hW : IsOpen W := isOpen_Ioi.preimage (continuous_const.mul ha.continuous)
  have han : ∀ x ∈ W, a x ≠ 0 := by
    intro x hx hax
    change 0 < s * a x at hx
    simp [hax] at hx
  have hd : ContDiffOn ℝ ∞ d W :=
    hc.contDiffOn.sub ((hb.contDiffOn.pow 2).div ha.contDiffOn han)
  let U : Set (ℝ × ℝ) := W ∩ (fun x => t * d x) ⁻¹' Ioi 0
  have hU : IsOpen U :=
    (continuousOn_const.mul hd.continuousOn).isOpen_inter_preimage hW isOpen_Ioi
  have h0 : (0 : ℝ × ℝ) ∈ U := ⟨hsa, htd⟩
  let u : ℝ × ℝ → ℝ := fun x => Real.sqrt (s * a x)
  let v : ℝ × ℝ → ℝ := fun x => b x / a x
  let w : ℝ × ℝ → ℝ := fun x => Real.sqrt (t * d x)
  have hu : ContDiffOn ℝ ∞ u U :=
    (contDiffOn_const.mul ha.contDiffOn).sqrt (fun x hx => ne_of_gt hx.1)
  have hv : ContDiffOn ℝ ∞ v U :=
    hb.contDiffOn.div ha.contDiffOn (fun x hx => han x hx.1)
  have hw : ContDiffOn ℝ ∞ w U :=
    (contDiffOn_const.mul (hd.mono inter_subset_left)).sqrt
      (fun x hx => ne_of_gt hx.2)
  obtain ⟨e, he0, hezero, heU, hecoe, he, hei⟩ :=
    exists_rescalingShear_localInverse hU h0 hu hv hw
      (ne_of_gt (Real.sqrt_pos.mpr hsa)) (ne_of_gt (Real.sqrt_pos.mpr htd))
  have he0t : (0 : ℝ × ℝ) ∈ e.target := hezero ▸ e.map_source he0
  refine ⟨e.symm, s, t, hs, ht, he0t, ?_, hei, he, ?_⟩
  · calc
      e.symm 0 = e.symm (e 0) := congrArg e.symm hezero.symm
      _ = 0 := e.left_inv he0
  · intro x hx
    have hux := heU (e.map_target hx)
    have heq := binary_quadratic_signed_squares (x := (e.symm x).1)
      (y := (e.symm x).2) hs2 ht2 hux.1 hux.2
    have hxy : rescalingShearMap u v w (e.symm x) = x := by
      rw [← hecoe]
      exact e.right_inv hx
    have hx1 := congrArg Prod.fst hxy
    have hx2 := congrArg Prod.snd hxy
    change u (e.symm x) * ((e.symm x).1 + v (e.symm x) * (e.symm x).2) = x.1 at hx1
    change w (e.symm x) * (e.symm x).2 = x.2 at hx2
    simpa only [← hx1, ← hx2] using heq

end Poincare.Analysis.Calculus.Morse
