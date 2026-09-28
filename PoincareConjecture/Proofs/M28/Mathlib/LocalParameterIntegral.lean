import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Energy
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set MeasureTheory
open scoped Topology ContDiff

noncomputable section
set_option autoImplicit false

namespace PoincareConjecture.ConjugateVariation

theorem continuousOn_intervalIntegral_of_continuousOn_prod
    {F : ℝ → ℝ → ℝ} {I : Set ℝ} {a b : ℝ}
    (hI : IsOpen I) (hab : a ≤ b)
    (hF : ContinuousOn (Function.uncurry F) (I ×ˢ Icc a b)) :
    ContinuousOn (fun s => ∫ t in a..b, F s t) I := by
  let : LocallyCompactSpace I := hI.locallyCompactSpace
  let f : I → ℝ → ℝ := fun s t => F s (projIcc a b hab t)
  have hf : Continuous (Function.uncurry f) := by
    apply hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp continuous_snd)))
    intro p
    exact ⟨p.1.property, (projIcc a b hab p.2).property⟩
  have hc : Continuous (fun s : I => ∫ t in Icc a b, f s t) :=
    continuous_parametric_integral_of_continuous hf isCompact_Icc
  apply continuousOn_iff_continuous_domRestrict.mpr
  have heq : (fun s : I => ∫ t in a..b, F s t) =
      (fun s : I => ∫ t in Icc a b, f s t) := by
    funext s
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp [f, projIcc_of_mem hab ht]
  change Continuous (fun s : I => ∫ t in a..b, F s t)
  rw [heq]
  exact hc

theorem contDiffOn_two_intervalIntegral_of_contDiffOn_box
    {F : ℝ → ℝ → ℝ} {a b s₀ r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F)
      (Ioo (s₀ - r) (s₀ + r) ×ˢ Ioo (a - r) (b + r))) :
    ContDiffOn ℝ 2 (fun s => ∫ t in a..b, F s t) (Ioo (s₀ - r) (s₀ + r)) := by
  let I := Ioo (s₀ - r) (s₀ + r)
  let J := Ioo (a - r) (b + r)
  have hU : IsOpen (I ×ˢ J) := isOpen_Ioo.prod isOpen_Ioo
  have hIccJ : Icc a b ⊆ J := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let G : ℝ → ℝ → ℝ := fun s t => deriv (fun σ => F σ t) s
  let K : ℝ → ℝ → ℝ := fun s t => deriv (fun σ => G σ t) s
  have hF1 : ContDiffOn ℝ 1 (Function.uncurry F) (I ×ˢ J) :=
    hF.of_le (by norm_num)
  have hG1 : ContDiffOn ℝ 1 (Function.uncurry G) (I ×ˢ J) := by
    have hfd : ContDiffOn ℝ 1 (fun p => fderiv ℝ (Function.uncurry F) p)
        (I ×ˢ J) := hF.fderiv_of_isOpen hU (by norm_num)
    refine (hfd.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr ?_
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact (hasDerivAt_partial_of_contDiffOn_box hF1 hs ht).deriv
  have hK : ContinuousOn (Function.uncurry K) (I ×ˢ J) := by
    have hfd := hG1.continuousOn_fderiv_of_isOpen hU le_rfl
    refine (hfd.clm_apply (continuousOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr ?_
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact (hasDerivAt_partial_of_contDiffOn_box hG1 hs ht).deriv
  have hcK : ContinuousOn (fun s => ∫ t in a..b, K s t) I :=
    continuousOn_intervalIntegral_of_continuousOn_prod isOpen_Ioo hab
      (hK.mono (prod_mono subset_rfl hIccJ))
  have hDF (s : ℝ) (hs : s ∈ I) :
      HasDerivAt (fun σ => ∫ t in a..b, F σ t) (∫ t in a..b, G s t) s :=
    hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hF1 hs
  have hDG (s : ℝ) (hs : s ∈ I) :
      HasDerivAt (fun σ => ∫ t in a..b, G σ t) (∫ t in a..b, K s t) s :=
    hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hG1 hs
  have hEG : ContDiffOn ℝ 1 (fun s => ∫ t in a..b, G s t) I := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun s hs => (hDG s hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hcK.congr fun s hs => (hDG s hs).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun s hs => (hDF s hs).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact hEG.congr fun s hs => (hDF s hs).deriv

end PoincareConjecture.ConjugateVariation
end
