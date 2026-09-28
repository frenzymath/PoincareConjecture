import PoincareConjecture.Proofs.M09.LocalSmoothInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

noncomputable def morseSquareMap (a b c : ℝ × ℝ → ℝ) (σ τ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (σ * a p) * (p.1 + b p / a p * p.2),
    Real.sqrt (τ * (c p - b p ^ 2 / a p)) * p.2)

@[simp] theorem morseSquareMap_zero (a b c : ℝ × ℝ → ℝ) (σ τ : ℝ) :
    morseSquareMap a b c σ τ 0 = 0 := by
  simp [morseSquareMap]

theorem morseSquareMap_identity (a b c : ℝ × ℝ → ℝ) (σ τ : ℝ)
    (hσ : σ * σ = 1) (hτ : τ * τ = 1) (p : ℝ × ℝ)
    (ha : 0 < σ * a p) (hd : 0 < τ * (c p - b p ^ 2 / a p)) :
    σ * (morseSquareMap a b c σ τ p).1 ^ 2 +
        τ * (morseSquareMap a b c σ τ p).2 ^ 2 =
      a p * p.1 ^ 2 + 2 * b p * p.1 * p.2 + c p * p.2 ^ 2 := by
  have ha0 : a p ≠ 0 := by intro h; simp [h] at ha
  have hσa : σ * (σ * a p) = a p := by rw [← mul_assoc, hσ, one_mul]
  have hτd : τ * (τ * (c p - b p ^ 2 / a p)) = c p - b p ^ 2 / a p := by
    rw [← mul_assoc, hτ, one_mul]
  simp only [morseSquareMap, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hd.le]
  rw [← mul_assoc σ, hσa, ← mul_assoc τ, hτd]
  field_simp
  ring

theorem exists_morse_square_chart (a b c : ℝ × ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
    (ha0 : a 0 ≠ 0) (hb0 : b 0 = 0) (hc0 : c 0 ≠ 0) :
    ∃ (σ τ : ℝ) (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)),
      σ * σ = 1 ∧ τ * τ = 1 ∧ 0 ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ p ∈ e.source,
        a p * p.1 ^ 2 + 2 * b p * p.1 * p.2 + c p * p.2 ^ 2 =
          σ * (e p).1 ^ 2 + τ * (e p).2 ^ 2 := by
  obtain ⟨σ, hσ, hσa⟩ : ∃ σ : ℝ, σ * σ = 1 ∧ 0 < σ * a 0 := by
    rcases lt_or_gt_of_ne ha0 with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
  obtain ⟨τ, hτ, hτc⟩ : ∃ τ : ℝ, τ * τ = 1 ∧ 0 < τ * c 0 := by
    rcases lt_or_gt_of_ne hc0 with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
  let d : ℝ × ℝ → ℝ := fun p => c p - b p ^ 2 / a p
  let W : Set (ℝ × ℝ) := {p | a p ≠ 0}
  have hW : IsOpen W := ha.continuous.isOpen_preimage _ isOpen_ne
  have hd : ContDiffOn ℝ ∞ d W :=
    hc.contDiffOn.sub ((hb.contDiffOn.pow 2).div ha.contDiffOn (fun _ hp => hp))
  let V : Set (ℝ × ℝ) := W ∩ {p | 0 < σ * a p}
  have hV : IsOpen V := hW.inter
    (isOpen_lt continuous_const (continuous_const.mul ha.continuous))
  let U : Set (ℝ × ℝ) := V ∩ {p | 0 < τ * d p}
  have hcont : ContinuousOn (fun p : ℝ × ℝ => τ * d p) V :=
    continuousOn_const.mul (hd.continuousOn.mono inter_subset_left)
  have hU : IsOpen U := hcont.isOpen_inter_preimage hV isOpen_Ioi
  have hd0 : d 0 = c 0 := by simp [d, hb0]
  have h0U : (0 : ℝ × ℝ) ∈ U :=
    ⟨⟨ha0, hσa⟩, by simpa only [mem_ofPred_eq, hd0] using hτc⟩
  have haU : ContDiffOn ℝ ∞ (fun p => Real.sqrt (σ * a p)) U :=
    (contDiffOn_const.mul ha.contDiffOn).sqrt (fun _ hp => ne_of_gt hp.1.2)
  have hdU : ContDiffOn ℝ ∞ (fun p => Real.sqrt (τ * d p)) U :=
    (contDiffOn_const.mul (hd.mono (fun _ hp => hp.1.1))).sqrt (fun _ hp => ne_of_gt hp.2)
  have hr : ContDiffOn ℝ ∞ (fun p => b p / a p) U :=
    hb.contDiffOn.div ha.contDiffOn (fun _ hp => hp.1.1)
  let g := morseSquareMap a b c σ τ
  have hg : ContDiffOn ℝ ∞ g U :=
    (haU.mul (contDiffOn_fst.add (hr.mul contDiffOn_snd))).prodMk (hdU.mul contDiffOn_snd)
  have hdg := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).add
    (((hr.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt.mul
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))))
  simp only [Prod.snd_zero, hb0, zero_div, zero_smul, add_zero] at hdg
  let α := Real.sqrt (σ * a 0)
  let β := Real.sqrt (τ * d 0)
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (α • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (β • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hα : 0 < α := Real.sqrt_pos.mpr hσa
  have hβ : 0 < β := Real.sqrt_pos.mpr (by simpa only [hd0] using hτc)
  have hdf : fderiv ℝ g 0 = D := by
    change fderiv ℝ (fun p : ℝ × ℝ =>
      (Real.sqrt (σ * a p) * (p.1 + b p / a p * p.2),
        Real.sqrt (τ * (c p - b p ^ 2 / a p)) * p.2)) 0 = D
    have hleft := ((haU.contDiffAt (hU.mem_nhds h0U)).differentiableAt
      (by simp)).hasFDerivAt.mul hdg
    have hright := ((hdU.contDiffAt (hU.mem_nhds h0U)).differentiableAt
      (by simp)).hasFDerivAt.mul (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ)))
    simpa [D, α, β, d, hb0] using (hleft.prodMk hright).fderiv
  have hDi : Function.Injective D := by
    intro p q hpq
    apply Prod.ext
    · exact mul_left_cancel₀ (ne_of_gt hα) (congrArg Prod.fst hpq)
    · exact mul_left_cancel₀ (ne_of_gt hβ) (congrArg Prod.snd hpq)
  have hDb : Function.Bijective (fderiv ℝ g 0) := by
    rw [hdf]
    exact ⟨hDi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hDi⟩
  obtain ⟨e, he0, heU, he, hei, _⟩ :=
    PoincareConjecture.Proofs.M09.exists_smooth_local_inverse g U hU hg 0 h0U hDb
  refine ⟨σ, τ, e, hσ, hτ, he0, ?_, ?_, hei, ?_⟩
  · rw [he]
    exact morseSquareMap_zero a b c σ τ
  · rw [he]
    exact hg.mono heU
  · intro p hp
    rw [he]
    exact (morseSquareMap_identity a b c σ τ hσ hτ p
      (heU hp).1.2 (heU hp).2).symm

end PoincareConjecture.M25.Topology3D
