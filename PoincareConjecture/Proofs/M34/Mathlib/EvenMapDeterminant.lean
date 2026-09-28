import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M34

theorem exists_not_injective_fderiv_of_eventually_even
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {U K : Set E} (hU : IsOpen U) (hK : IsPreconnected K)
    (hKU : K ⊆ U) {a : E} (ha : a ∈ K) (hna : -a ∈ K)
    (hf : ContDiffOn ℝ 1 f U) (hdim : Odd (Module.finrank ℝ E))
    (heven : (fun x => f (-x)) =ᶠ[𝓝 a] f) :
    ∃ x ∈ K, ¬ Function.Injective (fderiv ℝ f x) := by
  classical
  have hdf : DifferentiableAt ℝ f (-a) :=
    (hf.contDiffAt (hU.mem_nhds (hKU hna))).differentiableAt (by norm_num)
  have hcomp := fderiv_comp a hdf (differentiableAt_id.neg : DifferentiableAt ℝ (fun x : E => -x) a)
  have hsame := heven.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (f ∘ fun x : E => -x) a = fderiv ℝ f a at hsame
  rw [hcomp] at hsame
  have hneg : fderiv ℝ (fun x : E => -x) a = -ContinuousLinearMap.id ℝ E :=
    (hasFDerivAt_id a).neg.fderiv
  have hderiv : fderiv ℝ f (-a) = -fderiv ℝ f a := by
    ext v
    have h := congrArg (fun L : E →L[ℝ] E => L v) hsame
    simp only [ContinuousLinearMap.comp_apply, hneg, neg_apply,
      ContinuousLinearMap.id_apply, map_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  let D : E → ℝ := fun x => (fderiv ℝ f x).det
  have hdet : D (-a) = -D a := by
    dsimp [D]
    rw [hderiv]
    change LinearMap.det (-(fderiv ℝ f a).toLinearMap) = _
    rw [← neg_one_smul ℝ (fderiv ℝ f a).toLinearMap, LinearMap.det_smul,
      hdim.neg_one_pow, neg_one_mul]
  have hcontinuous : ContinuousOn D K :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num))).mono hKU
  by_contra! hinjective
  have hnonzero (x : E) (hx : x ∈ K) : D x ≠ 0 := by
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz)
      (LinearMap.ker_eq_bot.mpr (hinjective x hx))
  by_cases hsign : 0 ≤ D a
  · obtain ⟨x, hx, hz⟩ := hK.intermediate_value hna ha hcontinuous
      (show (0 : ℝ) ∈ Icc (D (-a)) (D a) from ⟨by rw [hdet]; linarith, hsign⟩)
    exact hnonzero x hx hz
  · obtain ⟨x, hx, hz⟩ := hK.intermediate_value ha hna hcontinuous
      (show (0 : ℝ) ∈ Icc (D a) (D (-a)) from
        ⟨(lt_of_not_ge hsign).le, by rw [hdet]; linarith⟩)
    exact hnonzero x hx hz

end PoincareConjecture.M34
