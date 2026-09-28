









import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Compactness.Compact





















noncomputable section

namespace PoincareConjecture.Conjugate.Realization

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {τ₀ τ₁ : ℝ} {ŷ Ŷ ĉ₀ ĉ₁ : ℝ → E}








def chartVariation (τ₀ τ₁ : ℝ) (ŷ Ŷ ĉ₀ ĉ₁ : ℝ → E) (p : ℝ × ℝ) : E :=
  ŷ p.2 + p.1 • Ŷ p.2
    + ((τ₁ - p.2) / (τ₁ - τ₀)) • (ĉ₀ p.1 - ŷ τ₀ - p.1 • Ŷ τ₀)
    + ((p.2 - τ₀) / (τ₁ - τ₀)) • (ĉ₁ p.1 - ŷ τ₁ - p.1 • Ŷ τ₁)




theorem chartVariation_left (hne : τ₀ ≠ τ₁) (s : ℝ) :
    chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, τ₀) = ĉ₀ s := by
  have h : τ₁ - τ₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  simp only [chartVariation, sub_self, zero_div, div_self h, one_smul, zero_smul, add_zero]
  abel



theorem chartVariation_right (hne : τ₀ ≠ τ₁) (s : ℝ) :
    chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, τ₁) = ĉ₁ s := by
  have h : τ₁ - τ₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  simp only [chartVariation, sub_self, zero_div, div_self h, one_smul, zero_smul, add_zero]
  abel



theorem chartVariation_zero (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁) (t : ℝ) :
    chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t) = ŷ t := by
  simp [chartVariation, hc₀, hc₁]


theorem chartVariation_comp_zero (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁) :
    (fun t : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t)) = ŷ :=
  funext (chartVariation_zero hc₀ hc₁)




theorem hasDerivAt_chartVariation_fst (hc₀' : HasDerivAt ĉ₀ (Ŷ τ₀) 0)
    (hc₁' : HasDerivAt ĉ₁ (Ŷ τ₁) 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t)) (Ŷ t) 0 := by
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) 0 := hasDerivAt_id 0
  have h1 : HasDerivAt (fun s : ℝ => ŷ t + s • Ŷ t) ((1 : ℝ) • Ŷ t) 0 :=
    (hid.smul_const (Ŷ t)).const_add _
  have h2 : HasDerivAt (fun s : ℝ => ĉ₀ s - ŷ τ₀ - s • Ŷ τ₀) (Ŷ τ₀ - (1 : ℝ) • Ŷ τ₀) 0 :=
    (hc₀'.sub_const (ŷ τ₀)).sub (hid.smul_const (Ŷ τ₀))
  have h3 : HasDerivAt (fun s : ℝ => ĉ₁ s - ŷ τ₁ - s • Ŷ τ₁) (Ŷ τ₁ - (1 : ℝ) • Ŷ τ₁) 0 :=
    (hc₁'.sub_const (ŷ τ₁)).sub (hid.smul_const (Ŷ τ₁))
  have h :=
    ((h1.add (h2.const_smul ((τ₁ - t) / (τ₁ - τ₀)))).add
      (h3.const_smul ((t - τ₀) / (τ₁ - τ₀))))
  have hfun :
      (fun s : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t)) =
        ((fun s : ℝ => ŷ t + s • Ŷ t) +
            ((τ₁ - t) / (τ₁ - τ₀)) •
              (fun s : ℝ => ĉ₀ s - ŷ τ₀ - s • Ŷ τ₀)) +
          ((t - τ₀) / (τ₁ - τ₀)) •
            (fun s : ℝ => ĉ₁ s - ŷ τ₁ - s • Ŷ τ₁) := by
    funext s
    rfl
  rw [hfun]
  simpa using h





theorem differentiableAt_chartVariation {s t : ℝ} (hy : DifferentiableAt ℝ ŷ t)
    (hY : DifferentiableAt ℝ Ŷ t) (h₀ : DifferentiableAt ℝ ĉ₀ s)
    (h₁ : DifferentiableAt ℝ ĉ₁ s) :
    DifferentiableAt ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (s, t) := by
  have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1) (s, t) := differentiableAt_fst
  have hsnd : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2) (s, t) := differentiableAt_snd
  have hy' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ŷ p.2) (s, t) := hy.comp _ hsnd
  have hY' : DifferentiableAt ℝ (fun p : ℝ × ℝ => Ŷ p.2) (s, t) := hY.comp _ hsnd
  have h₀' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₀ p.1) (s, t) := h₀.comp _ hfst
  have h₁' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₁ p.1) (s, t) := h₁.comp _ hfst
  have hl₀ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (τ₁ - p.2) / (τ₁ - τ₀)) (s, t) := by
    simp only [div_eq_mul_inv]
    exact ((differentiableAt_const τ₁).sub hsnd).mul_const (τ₁ - τ₀)⁻¹
  have hl₁ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.2 - τ₀) / (τ₁ - τ₀)) (s, t) := by
    simp only [div_eq_mul_inv]
    exact (hsnd.sub_const τ₀).mul_const (τ₁ - τ₀)⁻¹
  have hb₀ : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₀ p.1 - ŷ τ₀ - p.1 • Ŷ τ₀) (s, t) :=
    (h₀'.sub_const (ŷ τ₀)).sub (hfst.smul (differentiableAt_const (Ŷ τ₀)))
  have hb₁ : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₁ p.1 - ŷ τ₁ - p.1 • Ŷ τ₁) (s, t) :=
    (h₁'.sub_const (ŷ τ₁)).sub (hfst.smul (differentiableAt_const (Ŷ τ₁)))
  exact ((hy'.add (hfst.smul hY')).add (hl₀.smul hb₀)).add (hl₁.smul hb₁)

set_option linter.unusedVariables false in




theorem fderiv_chartVariation_snd_zero (hne : τ₀ ≠ τ₁)
    (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁)
    (hc₀' : HasDerivAt ĉ₀ (Ŷ τ₀) 0) (hc₁' : HasDerivAt ĉ₁ (Ŷ τ₁) 0)
    {t : ℝ} (hy : DifferentiableAt ℝ ŷ t) (hY : DifferentiableAt ℝ Ŷ t) :
    fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t) (1, 0) = Ŷ t := by
  have hdiff := differentiableAt_chartVariation (τ₀ := τ₀) (τ₁ := τ₁)
    (s := (0 : ℝ)) hy hY hc₀'.differentiableAt hc₁'.differentiableAt
  have hF : HasFDerivAt (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁)
      (fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t)) (0, t) := hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => ((s, t) : ℝ × ℝ)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t)
  have h1 := hF.comp_hasDerivAt 0 hcurve
  have h2 := hasDerivAt_chartVariation_fst (ŷ := ŷ) (τ₀ := τ₀) (τ₁ := τ₁) hc₀' hc₁' t
  exact (h1.unique h2)

set_option linter.unusedVariables false in



theorem fderiv_chartVariation_fst_zero (hne : τ₀ ≠ τ₁)
    (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁)
    (hc₀' : HasDerivAt ĉ₀ (Ŷ τ₀) 0) (hc₁' : HasDerivAt ĉ₁ (Ŷ τ₁) 0)
    {t : ℝ} {y' : E} (hy : HasDerivAt ŷ y' t) (hY : DifferentiableAt ℝ Ŷ t) :
    fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t) (0, 1) = y' := by
  have hdiff := differentiableAt_chartVariation (τ₀ := τ₀) (τ₁ := τ₁)
    (s := (0 : ℝ)) hy.differentiableAt hY hc₀'.differentiableAt hc₁'.differentiableAt
  have hF : HasFDerivAt (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁)
      (fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t)) (0, t) := hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => ((0, t) : ℝ × ℝ)) (0, 1) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have h1 := hF.comp_hasDerivAt t hcurve
  have h2 : HasDerivAt (fun t : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t)) y' t := by
    rw [chartVariation_comp_zero hc₀ hc₁]; exact hy
  exact (h1.unique h2)

set_option linter.unusedVariables false in




theorem contDiff_chartVariation {n : WithTop ℕ∞} (hne : τ₀ ≠ τ₁)
    (hŷ : ContDiff ℝ n ŷ) (hŶ : ContDiff ℝ n Ŷ)
    (hc₀ : ContDiff ℝ n ĉ₀) (hc₁ : ContDiff ℝ n ĉ₁) :
    ContDiff ℝ n (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) := by
  have hfst : ContDiff ℝ n (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have hsnd : ContDiff ℝ n (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hy' : ContDiff ℝ n (fun p : ℝ × ℝ => ŷ p.2) := hŷ.comp hsnd
  have hY' : ContDiff ℝ n (fun p : ℝ × ℝ => Ŷ p.2) := hŶ.comp hsnd
  have h₀' : ContDiff ℝ n (fun p : ℝ × ℝ => ĉ₀ p.1) := hc₀.comp hfst
  have h₁' : ContDiff ℝ n (fun p : ℝ × ℝ => ĉ₁ p.1) := hc₁.comp hfst
  refine ((hy'.add (hfst.smul hY')).add ?_).add ?_
  · exact ((((contDiff_const).sub hsnd).div_const _)).smul
      ((h₀'.sub (contDiff_const)).sub (hfst.smul contDiff_const))
  · exact (((hsnd.sub (contDiff_const)).div_const _)).smul
      ((h₁'.sub (contDiff_const)).sub (hfst.smul contDiff_const))





theorem exists_forall_mem_of_isOpen_of_continuous {U : Set E} (hU : IsOpen U)
    (hcont : Continuous (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁))
    (hmem : ∀ t ∈ Set.Icc τ₀ τ₁, chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t) ∈ U) :
    ∃ ε > 0, ∀ s ∈ Set.Ioo (-ε) ε, ∀ t ∈ Set.Icc τ₀ τ₁,
      chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t) ∈ U := by
  have hK : IsCompact (Set.Icc τ₀ τ₁) := isCompact_Icc
  have key : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      ∀ t ∈ Set.Icc τ₀ τ₁, chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun t ht => ?_)
    have hpre : (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) ⁻¹' U ∈ 𝓝 ((0 : ℝ), t) :=
      (hU.preimage hcont).mem_nhds (hmem t ht)
    filter_upwards [hpre] with z hz using hz
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  refine ⟨ε, hε, fun s hs t ht => ?_⟩
  refine hkey ?_ t ht
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact ⟨hs.1, hs.2⟩

end PoincareConjecture.Conjugate.Realization

end
