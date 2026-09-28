import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue








set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem fderiv_neg_of_eventually_even {f : E → E} {x : E}
    (hf : DifferentiableAt ℝ f (-x))
    (heven : ∀ᶠ y in 𝓝 x, f (-y) = f y) :
    fderiv ℝ f (-x) = -fderiv ℝ f x := by
  have hd := (hf.hasFDerivAt.comp x (hasFDerivAt_id x).neg).congr_of_eventuallyEq
    (heven.mono fun y hy => hy.symm)
  have heq : fderiv ℝ f x = -fderiv ℝ f (-x) := by
    simpa only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using hd.fderiv
  simpa only [neg_neg] using congrArg Neg.neg heq.symm



theorem exists_det_fderiv_eq_zero_of_locally_even [FiniteDimensional ℝ E]
    (hdim : Odd (Module.finrank ℝ E)) {s : Set E} (hs : IsConnected s)
    (hneg : ∀ x ∈ s, -x ∈ s) {f : E → E}
    (hf : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (heven : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, f (-y) = f y) :
    ∃ x ∈ s, (fderiv ℝ f x).det = 0 := by
  let d : E → ℝ := fun x => (fderiv ℝ f x).det
  have hd : ContinuousOn d s := fun x hx =>
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hf x hx).continuousAt_fderiv (by norm_num))).continuousWithinAt
  have hodd : ∀ x ∈ s, d (-x) = -d x := by
    intro x hx
    dsimp only [d]
    rw [fderiv_neg_of_eventually_even
      ((hf (-x) (hneg x hx)).differentiableAt (by norm_num)) (heven x hx)]
    change LinearMap.det (-((fderiv ℝ f x) : E →ₗ[ℝ] E)) = _
    rw [← neg_one_smul ℝ, LinearMap.det_smul, hdim.neg_one_pow]
    simp only [neg_one_mul, ContinuousLinearMap.det]
  obtain ⟨x, hx⟩ := hs.nonempty
  obtain h | h := le_total (d x) 0
  · obtain ⟨y, hy, hyzero⟩ := hs.isPreconnected.intermediate_value hx (hneg x hx) hd
      (show 0 ∈ Icc (d x) (d (-x)) by rw [hodd x hx]; exact ⟨h, neg_nonneg.mpr h⟩)
    exact ⟨y, hy, hyzero⟩
  · obtain ⟨y, hy, hyzero⟩ := hs.isPreconnected.intermediate_value (hneg x hx) hx hd
      (show 0 ∈ Icc (d (-x)) (d x) by rw [hodd x hx]; exact ⟨neg_nonpos.mpr h, h⟩)
    exact ⟨y, hy, hyzero⟩



theorem not_forall_isInvertible_fderiv_of_locally_even [FiniteDimensional ℝ E]
    (hdim : Odd (Module.finrank ℝ E)) {s : Set E} (hs : IsConnected s)
    (hneg : ∀ x ∈ s, -x ∈ s) {f : E → E}
    (hf : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (heven : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, f (-y) = f y) :
    ¬ ∀ x ∈ s, (fderiv ℝ f x).IsInvertible := by
  intro hinv
  obtain ⟨x, hx, hzero⟩ := exists_det_fderiv_eq_zero_of_locally_even hdim hs hneg hf heven
  obtain ⟨e, he⟩ := hinv x hx
  have hne := e.toLinearEquiv.isUnit_det'.ne_zero
  apply hne
  rw [← he] at hzero
  convert hzero using 1
  congr 1



theorem not_forall_isInvertible_fderiv_of_even [FiniteDimensional ℝ E]
    (hdim : Odd (Module.finrank ℝ E)) {s : Set E} (hs : IsConnected s)
    (hopen : IsOpen s) (hneg : ∀ x ∈ s, -x ∈ s) {f : E → E}
    (hf : ContDiffOn ℝ 1 f s) (heven : ∀ x ∈ s, f (-x) = f x) :
    ¬ ∀ x ∈ s, (fderiv ℝ f x).IsInvertible := by
  apply not_forall_isInvertible_fderiv_of_locally_even hdim hs hneg
  · exact fun x hx => hf.contDiffAt (hopen.mem_nhds hx)
  · intro x hx
    exact Filter.eventually_of_mem (hopen.mem_nhds hx) heven

end Poincare.Manifold
