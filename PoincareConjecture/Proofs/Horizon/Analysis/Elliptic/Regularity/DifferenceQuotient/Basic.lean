/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Sobolev/Tools/DifferenceQuotient.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise

namespace Poincare.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def diffQuot (i : Fin d) (h : ℝ) (v : E → ℝ) : E → ℝ :=
  fun x =>
    if h = 0 then 0 else
      (v (x + h • EuclideanSpace.single i 1) - v x) / h

noncomputable def translate (i : Fin d) (h : ℝ) (v : E → ℝ) : E → ℝ :=
  fun x => v (x + h • EuclideanSpace.single i 1)

omit [NeZero d] in
@[simp] lemma translate_zero_h (i : Fin d) (v : E → ℝ) :
    translate i 0 v = v := by
  ext x
  simp [translate]

omit [NeZero d] in
@[simp] lemma diffQuot_zero_h (i : Fin d) (v : E → ℝ) :
    diffQuot i 0 v = 0 := by
  ext x
  simp [diffQuot]

omit [NeZero d] in
lemma diffQuot_apply_of_ne (i : Fin d) {h : ℝ} (hh : h ≠ 0) (v : E → ℝ)
    (x : E) :
    diffQuot i h v x =
      (v (x + h • EuclideanSpace.single i 1) - v x) / h := by
  simp [diffQuot, hh]

omit [NeZero d] in
lemma diffQuot_eq_translate_sub_div (i : Fin d) {h : ℝ} (hh : h ≠ 0)
    (v : E → ℝ) :
    diffQuot i h v = fun x => (translate i h v x - v x) / h := by
  ext x
  simp [diffQuot, translate, hh]

omit [NeZero d] in
@[simp] lemma translate_add (i : Fin d) (h : ℝ) (v w : E → ℝ) :
    translate i h (v + w) = translate i h v + translate i h w := by
  ext x
  simp [translate, Pi.add_apply]

omit [NeZero d] in
@[simp] lemma translate_sub (i : Fin d) (h : ℝ) (v w : E → ℝ) :
    translate i h (v - w) = translate i h v - translate i h w := by
  ext x
  simp [translate, Pi.sub_apply]

omit [NeZero d] in
@[simp] lemma translate_smul (i : Fin d) (h c : ℝ) (v : E → ℝ) :
    translate i h (c • v) = c • translate i h v := by
  ext x
  simp [translate, Pi.smul_apply]

omit [NeZero d] in
@[simp] lemma translate_neg (i : Fin d) (h : ℝ) (v : E → ℝ) :
    translate i h (-v) = -translate i h v := by
  ext x
  simp [translate, Pi.neg_apply]

omit [NeZero d] in
@[simp] lemma translate_zero (i : Fin d) (h : ℝ) :
    translate i h (0 : E → ℝ) = 0 := by
  ext x
  simp [translate]

omit [NeZero d] in
@[simp] lemma diffQuot_add (i : Fin d) (h : ℝ) (v w : E → ℝ) :
    diffQuot i h (v + w) = diffQuot i h v + diffQuot i h w := by
  ext x
  by_cases hh : h = 0
  · simp [diffQuot, hh]
  · simp only [diffQuot, hh, ↓reduceIte, Pi.add_apply]
    ring

omit [NeZero d] in
@[simp] lemma diffQuot_smul (i : Fin d) (h c : ℝ) (v : E → ℝ) :
    diffQuot i h (c • v) = c • diffQuot i h v := by
  ext x
  by_cases hh : h = 0
  · simp [diffQuot, hh]
  · simp only [diffQuot, hh, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    ring

omit [NeZero d] in
@[simp] lemma diffQuot_sub (i : Fin d) (h : ℝ) (v w : E → ℝ) :
    diffQuot i h (v - w) = diffQuot i h v - diffQuot i h w := by
  ext x
  by_cases hh : h = 0
  · simp [diffQuot, hh]
  · simp only [diffQuot, hh, ↓reduceIte, Pi.sub_apply]
    ring

omit [NeZero d] in
@[simp] lemma diffQuot_zero (i : Fin d) (h : ℝ) :
    diffQuot i h (0 : E → ℝ) = 0 := by
  ext x
  by_cases hh : h = 0
  · simp [diffQuot, hh]
  · simp [diffQuot, hh]

omit [NeZero d] in
@[simp] lemma diffQuot_neg (i : Fin d) (h : ℝ) (v : E → ℝ) :
    diffQuot i h (-v) = -diffQuot i h v := by
  ext x
  by_cases hh : h = 0
  · simp [diffQuot, hh]
  · simp only [diffQuot, hh, ↓reduceIte, Pi.neg_apply]
    ring

omit [NeZero d] in
lemma measurable_translate (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : Measurable v) :
    Measurable (translate i h v) := by
  have hadd : Measurable (fun x : E => x + h • EuclideanSpace.single i 1) :=
    measurable_id.add_const _
  exact hv.comp hadd

omit [NeZero d] in
lemma measurable_diffQuot (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : Measurable v) :
    Measurable (diffQuot i h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    exact measurable_const
  · have hT : Measurable (fun x : E => v (x + h • EuclideanSpace.single i 1)) :=
      measurable_translate (d := d) i h hv
    have hd : Measurable (fun x : E =>
        (v (x + h • EuclideanSpace.single i 1) - v x) / h) :=
      ((hT.sub hv).div_const h)
    have heq : diffQuot i h v =
        fun x => (v (x + h • EuclideanSpace.single i 1) - v x) / h := by
      ext x; simp [diffQuot, hh]
    rw [heq]; exact hd

omit [NeZero d] in
lemma continuous_translate (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : Continuous v) : Continuous (translate i h v) := by
  have hadd : Continuous (fun x : E => x + h • EuclideanSpace.single i 1) :=
    continuous_id.add continuous_const
  exact hv.comp hadd

omit [NeZero d] in
lemma continuous_diffQuot_of_continuous (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : Continuous v) : Continuous (diffQuot i h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    exact continuous_const
  · have hT : Continuous (fun x : E => v (x + h • EuclideanSpace.single i 1)) :=
      continuous_translate (d := d) i h hv
    have hd : Continuous
        (fun x : E => (v (x + h • EuclideanSpace.single i 1) - v x) / h) :=
      (hT.sub hv).div_const h
    have heq : diffQuot i h v =
        fun x => (v (x + h • EuclideanSpace.single i 1) - v x) / h := by
      ext x; simp [diffQuot, hh]
    rw [heq]; exact hd

omit [NeZero d] in
lemma aestronglyMeasurable_diffQuot
    (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : AEStronglyMeasurable v volume) :
    AEStronglyMeasurable (diffQuot i h v) volume := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    exact aestronglyMeasurable_const
  · have hMP : MeasurePreserving
        (fun x : E => x + h • EuclideanSpace.single i 1) volume volume :=
      measurePreserving_add_right volume _
    have hT : AEStronglyMeasurable
        (fun x : E => v (x + h • EuclideanSpace.single i 1)) volume :=
      hv.comp_measurePreserving hMP
    have hd : AEStronglyMeasurable
        (fun x : E => (v (x + h • EuclideanSpace.single i 1) - v x) / h)
        volume := by
      have hSub : AEStronglyMeasurable
          (fun x : E => v (x + h • EuclideanSpace.single i 1) - v x) volume :=
        hT.sub hv
      have heq_div :
          (fun x : E =>
              (v (x + h • EuclideanSpace.single i 1) - v x) / h) =
            (fun x : E =>
              (v (x + h • EuclideanSpace.single i 1) - v x) * h⁻¹) := by
        funext x; rw [div_eq_mul_inv]
      rw [heq_div]
      exact hSub.mul_const h⁻¹
    have heq : diffQuot i h v =
        fun x => (v (x + h • EuclideanSpace.single i 1) - v x) / h := by
      ext x; simp [diffQuot, hh]
    rw [heq]; exact hd

omit [NeZero d] in
lemma tendsto_diffQuot_of_contDiff
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (i : Fin d) (x : E) :
    Tendsto (fun h : ℝ => diffQuot i h v x) (𝓝[≠] 0)
      (𝓝 ((fderiv ℝ v x) (EuclideanSpace.single i 1))) := by
  have hdiff : Differentiable ℝ v := hv.differentiable_one
  set e : E := EuclideanSpace.single i (1 : ℝ) with he
  have hLineDiff :
      HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    have h_smulRight : HasDerivAt (fun s : ℝ => s • e) e 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const e
    simpa using h_smulRight.const_add x
  have hv_at : HasFDerivAt v (fderiv ℝ v x) x :=
    (hdiff x).hasFDerivAt
  have hComp :
      HasDerivAt (fun t : ℝ => v (x + t • e))
        ((fderiv ℝ v x) e) 0 := by
    have : x + (0 : ℝ) • e = x := by simp
    have hv_at_at0 : HasFDerivAt v (fderiv ℝ v x) (x + (0 : ℝ) • e) := by
      rw [this]; exact hv_at
    exact hv_at_at0.comp_hasDerivAt 0 hLineDiff
  have hpre :
      Tendsto (fun t : ℝ =>
        t⁻¹ • ((fun s : ℝ => v (x + s • e)) (0 + t) -
          (fun s : ℝ => v (x + s • e)) 0))
        (𝓝[≠] 0)
        (𝓝 ((fderiv ℝ v x) e)) :=
    hComp.tendsto_slope_zero
  have hCong :
      ∀ᶠ t : ℝ in 𝓝[≠] 0,
        t⁻¹ • ((fun s : ℝ => v (x + s • e)) (0 + t) -
              (fun s : ℝ => v (x + s • e)) 0) =
          diffQuot i t v x := by
    refine eventually_nhdsWithin_iff.mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht0 : t ≠ 0 := ht
    change t⁻¹ • (v (x + (0 + t) • e) - v (x + (0 : ℝ) • e)) = diffQuot i t v x
    have h0 : x + (0 : ℝ) • e = x := by simp
    have h1 : (0 : ℝ) + t = t := by ring
    simp only [h0, h1, smul_eq_mul, diffQuot, ht0, ↓reduceIte, e]
    rw [div_eq_inv_mul]
  exact hpre.congr' hCong

omit [NeZero d] in
private lemma measurePreserving_translate (i : Fin d) (h : ℝ) :
    MeasurePreserving
      (fun x : E => x + h • EuclideanSpace.single i 1) volume volume :=
  measurePreserving_add_right volume _

omit [NeZero d] in
lemma memLp_translate
    {p : ℝ≥0∞} (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : MemLp v p volume) :
    MemLp (translate i h v) p volume := by
  have hMP := measurePreserving_translate (d := d) i h
  have h_aesm : AEStronglyMeasurable (translate i h v) volume :=
    hv.aestronglyMeasurable.comp_measurePreserving hMP
  refine ⟨h_aesm, ?_⟩
  unfold translate
  have h_eq :
      eLpNorm (fun x : E => v (x + h • EuclideanSpace.single i 1)) p volume =
        eLpNorm v p volume :=
    eLpNorm_comp_measurePreserving hv.aestronglyMeasurable hMP
  rw [h_eq]; exact hv.eLpNorm_lt_top

omit [NeZero d] in
lemma integrable_translate
    (i : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : Integrable v volume) :
    Integrable (translate i h v) volume := by
  have hMP := measurePreserving_translate (d := d) i h
  exact hMP.integrable_comp_of_integrable hv

omit [NeZero d] in
private lemma holder_two_two : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
  constructor
  rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
  rw [ENNReal.inv_two_add_inv_two]

omit [NeZero d] in
lemma integrable_mul_of_memLp_two
    {f g : E → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => f x * g x) volume := by
  have := holder_two_two
  have h := MemLp.integrable_mul (μ := (volume : Measure E))
    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hf hg
  exact h.congr (Filter.Eventually.of_forall fun _ => rfl)

omit [NeZero d] in
theorem integral_diffQuot_mul_eq_neg_integral_mul_diffQuot
    (i : Fin d) {h : ℝ} (hh : h ≠ 0) {f g : E → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ x, diffQuot i h f x * g x ∂(volume : Measure E) =
      -∫ x, f x * diffQuot i (-h) g x ∂(volume : Measure E) := by
  set e : E := EuclideanSpace.single i (1 : ℝ) with he
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have hfg_int : Integrable (fun x => f x * g x) volume :=
    integrable_mul_of_memLp_two (d := d) hf hg
  have hf_translate_memLp : MemLp (translate i h f) 2 volume :=
    memLp_translate (d := d) (p := 2) i h hf
  have hg_translate_memLp : MemLp (translate i (-h) g) 2 volume :=
    memLp_translate (d := d) (p := 2) i (-h) hg
  have hf_translate_int :
      Integrable (fun x => translate i h f x * g x) volume :=
    integrable_mul_of_memLp_two (d := d) hf_translate_memLp hg
  have hg_translate_int :
      Integrable (fun x => f x * translate i (-h) g x) volume :=
    integrable_mul_of_memLp_two (d := d) hf hg_translate_memLp
  have hLHS_pointwise : ∀ x : E,
      diffQuot i h f x * g x =
        (translate i h f x * g x - f x * g x) / h := by
    intro x
    rw [diffQuot_apply_of_ne (d := d) i hh f x]
    change (f (x + h • e) - f x) / h * g x =
      (translate i h f x * g x - f x * g x) / h
    change (f (x + h • e) - f x) / h * g x =
      (f (x + h • e) * g x - f x * g x) / h
    rw [div_mul_eq_mul_div, sub_mul]
  have hRHS_pointwise : ∀ x : E,
      f x * diffQuot i (-h) g x =
        (f x * translate i (-h) g x - f x * g x) / (-h) := by
    intro x
    rw [diffQuot_apply_of_ne (d := d) i hnh g x]
    change f x * ((g (x + (-h) • e) - g x) / (-h)) =
      (f x * translate i (-h) g x - f x * g x) / (-h)
    change f x * ((g (x + (-h) • e) - g x) / (-h)) =
      (f x * g (x + (-h) • e) - f x * g x) / (-h)
    rw [mul_div_assoc', mul_sub]
  have hLHS_decomp :
      ∫ x, diffQuot i h f x * g x ∂(volume : Measure E) =
        ((∫ x, translate i h f x * g x ∂(volume : Measure E)) -
            ∫ x, f x * g x ∂(volume : Measure E)) / h := by
    have heq_fun : (fun x => diffQuot i h f x * g x) =
        (fun x => (translate i h f x * g x - f x * g x) / h) := by
      ext x; exact hLHS_pointwise x
    rw [heq_fun, integral_div, integral_sub hf_translate_int hfg_int]
  have hRHS_decomp :
      ∫ x, f x * diffQuot i (-h) g x ∂(volume : Measure E) =
        ((∫ x, f x * translate i (-h) g x ∂(volume : Measure E)) -
            ∫ x, f x * g x ∂(volume : Measure E)) / (-h) := by
    have heq_fun : (fun x => f x * diffQuot i (-h) g x) =
        (fun x => (f x * translate i (-h) g x - f x * g x) / (-h)) := by
      ext x; exact hRHS_pointwise x
    rw [heq_fun, integral_div, integral_sub hg_translate_int hfg_int]
  have h_subst :
      ∫ x, f (x + h • e) * g x ∂(volume : Measure E) =
        ∫ x, f x * g (x + (-h) • e) ∂(volume : Measure E) := by
    have hint :=
      integral_add_right_eq_self
        (μ := (volume : Measure E))
        (f := fun x : E => f (x + h • e) * g x)
        ((-h) • e)
    have hsimp : ∀ x : E,
        f ((x + (-h) • e) + h • e) * g (x + (-h) • e) =
          f x * g (x + (-h) • e) := by
      intro x
      have hsmul : (-h) • e + h • e = (0 : E) := by
        rw [← add_smul]; simp
      have hcoll : (x + (-h) • e) + h • e = x := by
        rw [add_assoc, hsmul, add_zero]
      rw [hcoll]
    rw [show (∫ x, f (x + h • e) * g x ∂(volume : Measure E)) =
        ∫ x, f ((x + (-h) • e) + h • e) * g (x + (-h) • e)
          ∂(volume : Measure E) from hint.symm]
    refine integral_congr_ae ?_
    filter_upwards with x using hsimp x
  have hLHS_subst :
      ∫ x, translate i h f x * g x ∂(volume : Measure E) =
        ∫ x, f x * translate i (-h) g x ∂(volume : Measure E) := by
    have h1 :
        ∫ x, translate i h f x * g x ∂(volume : Measure E) =
          ∫ x, f (x + h • e) * g x ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      change f (x + h • EuclideanSpace.single i 1) * g x = f (x + h • e) * g x
      rfl
    have h2 :
        ∫ x, f x * translate i (-h) g x ∂(volume : Measure E) =
          ∫ x, f x * g (x + (-h) • e) ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      change f x * g (x + (-h) • EuclideanSpace.single i 1) =
        f x * g (x + (-h) • e)
      rfl
    rw [h1, h2, h_subst]
  rw [hLHS_decomp, hRHS_decomp, hLHS_subst]
  rw [div_neg, neg_neg]

omit [NeZero d] in
lemma diffQuot_eq_integral_partialDeriv
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (i : Fin d) {h : ℝ} (hh : h ≠ 0)
    (x : E) :
    diffQuot i h v x =
      ∫ s in Set.Ioc (0 : ℝ) 1,
        (fderiv ℝ v (x + (s * h) • EuclideanSpace.single i 1))
          (EuclideanSpace.single i 1) := by
  set e : E := EuclideanSpace.single i (1 : ℝ) with he
  have hdiff : Differentiable ℝ v := hv.differentiable_one
  set γ : ℝ → E := fun s => x + (s * h) • e with hγ_def
  have hγ_deriv : ∀ s, HasDerivAt γ (h • e) s := by
    intro s
    have h_mul_pre : HasDerivAt (fun t : ℝ => t * h) (1 * h) s :=
      (hasDerivAt_id s).mul_const h
    have h_mul : HasDerivAt (fun t : ℝ => t * h) h s := by
      simpa using h_mul_pre
    have hsmul : HasDerivAt (fun t : ℝ => (t * h) • e) (h • e) s := by
      simpa using h_mul.smul_const e
    simpa [γ] using hsmul.const_add x
  have hcomp_deriv : ∀ s, HasDerivAt (v ∘ γ)
      ((fderiv ℝ v (γ s)) (h • e)) s := by
    intro s
    have hv_at : HasFDerivAt v (fderiv ℝ v (γ s)) (γ s) :=
      (hdiff (γ s)).hasFDerivAt
    have h_comp : HasDerivAt (fun t : ℝ => v (γ t))
        ((fderiv ℝ v (γ s)) (h • e)) s :=
      hv_at.comp_hasDerivAt s (hγ_deriv s)
    exact h_comp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hcomp_deriv_factored : ∀ s,
      HasDerivAt (v ∘ γ) (h * (fderiv ℝ v (γ s)) e) s := by
    intro s
    have hcd := hcomp_deriv s
    have hfact : (fderiv ℝ v (γ s)) (h • e) = h * (fderiv ℝ v (γ s)) e := by
      rw [(fderiv ℝ v (γ s)).map_smul, smul_eq_mul]
    rw [hfact] at hcd
    exact hcd
  have hfd_cont : Continuous (fun y : E => fderiv ℝ v y) :=
    hv.continuous_fderiv one_ne_zero
  have hγ_cont : Continuous γ :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  have hint_cont : Continuous (fun s : ℝ => (fderiv ℝ v (γ s)) e) :=
    (hfd_cont.comp hγ_cont).clm_apply continuous_const
  have h_intervalInt :
      IntervalIntegrable (fun s : ℝ => h * (fderiv ℝ v (γ s)) e)
        (volume : Measure ℝ) 0 1 := by
    refine (Continuous.continuousOn ?_).intervalIntegrable
    exact continuous_const.mul hint_cont
  have hFTC :
      ∫ s in (0 : ℝ)..1, h * (fderiv ℝ v (γ s)) e =
        (v ∘ γ) 1 - (v ∘ γ) 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := v ∘ γ) (f' := fun s => h * (fderiv ℝ v (γ s)) e)
      (a := 0) (b := 1) (fun s _ => hcomp_deriv_factored s) h_intervalInt
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ 1 = x + h • e := by
    simp [γ, one_mul]
  have hIoc :
      ∫ s in (0 : ℝ)..1, h * (fderiv ℝ v (γ s)) e =
        ∫ s in Set.Ioc (0 : ℝ) 1, h * (fderiv ℝ v (γ s)) e :=
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hPullConst :
      ∫ s in Set.Ioc (0 : ℝ) 1, h * (fderiv ℝ v (γ s)) e =
        h * ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e := by
    rw [integral_const_mul]
  have hCombined :
      h * ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e =
        v (x + h • e) - v x := by
    rw [← hPullConst, ← hIoc, hFTC, Function.comp, Function.comp, hγ0, hγ1]
  have hdiv : ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e =
        (v (x + h • e) - v x) / h := by
    have h1 :
        (h * ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e) / h =
          (v (x + h • e) - v x) / h := by
      rw [hCombined]
    have h2 :
        (h * ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e) / h =
          ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e := by
      rw [mul_comm, mul_div_assoc, div_self hh, mul_one]
    rw [← h2, h1]
  have hrewrite_goal :
      diffQuot i h v x =
        ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ v (γ s)) e := by
    rw [diffQuot_apply_of_ne (d := d) i hh v x]
    rw [hdiv]
  rw [hrewrite_goal]

omit [NeZero d] in
lemma sq_diffQuot_le_integral_sq_partialDeriv
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (i : Fin d) {h : ℝ} (hh : h ≠ 0)
    (x : E) :
    (diffQuot i h v x) ^ 2 ≤
      ∫ s in Set.Ioc (0 : ℝ) 1,
        ((fderiv ℝ v (x + (s * h) • EuclideanSpace.single i 1))
          (EuclideanSpace.single i 1)) ^ 2 := by
  set e : E := EuclideanSpace.single i (1 : ℝ) with he
  set γ : ℝ → E := fun s => x + (s * h) • e with hγ_def
  set f : ℝ → ℝ := fun s => (fderiv ℝ v (γ s)) e with hf_def
  have hμprob :
      IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Ioc]
  have hfd_cont : Continuous (fun y : E => fderiv ℝ v y) :=
    hv.continuous_fderiv one_ne_zero
  have hγ_cont : Continuous γ :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  have hf_cont : Continuous f := by
    change Continuous (fun s => (fderiv ℝ v (γ s)) e)
    exact (hfd_cont.comp hγ_cont).clm_apply continuous_const
  have hf_int :
      Integrable f ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    hf_cont.integrableOn_Ioc (a := 0) (b := 1)
  have hf2_int :
      Integrable (fun s => f s ^ 2)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hcont : Continuous (fun s : ℝ => f s ^ 2) := hf_cont.pow 2
    exact hcont.integrableOn_Ioc (a := 0) (b := 1)
  have hFTC : diffQuot i h v x = ∫ s in Set.Ioc (0 : ℝ) 1, f s :=
    diffQuot_eq_integral_partialDeriv (d := d) hv i hh x
  have hsq_convex : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) := by
    refine Even.convexOn_pow (n := 2) ?_
    exact ⟨1, by ring⟩
  have hcont_on : ContinuousOn (fun t : ℝ => t ^ 2) Set.univ :=
    (continuous_pow 2).continuousOn
  have hfs :
      ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
        f s ∈ (Set.univ : Set ℝ) := by
    filter_upwards with s using mem_univ _
  have hJensen :
      (∫ s in Set.Ioc (0 : ℝ) 1, f s) ^ 2 ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, (f s) ^ 2 :=
    hsq_convex.map_integral_le hcont_on isClosed_univ hfs hf_int hf2_int
  rw [hFTC]
  exact hJensen

omit [NeZero d] in
lemma sq_diffQuot_le_integral_indicator
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (i : Fin d) {h : ℝ} (hh : h ≠ 0)
    {Ω : Set E} (hΩ : MeasurableSet Ω)
    {Ω' : Set E} (hΩ' : MeasurableSet Ω')
    (h_admissible : ∀ x ∈ Ω', ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      x + (s * h) • EuclideanSpace.single i 1 ∈ Ω)
    (x : E) (hx : x ∈ Ω') :
    (diffQuot i h v x) ^ 2 ≤
      ∫ s in Set.Ioc (0 : ℝ) 1,
        Ω.indicator (fun y => ((fderiv ℝ v y) (EuclideanSpace.single i 1)) ^ 2)
          (x + (s * h) • EuclideanSpace.single i 1) := by
  let _ := hΩ
  let _ := hΩ'
  have hbase :
      (diffQuot i h v x) ^ 2 ≤
        ∫ s in Set.Ioc (0 : ℝ) 1,
          ((fderiv ℝ v (x + (s * h) • EuclideanSpace.single i 1))
            (EuclideanSpace.single i 1)) ^ 2 :=
    sq_diffQuot_le_integral_sq_partialDeriv (d := d) hv i hh x
  have hpt :
      ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
        ((fderiv ℝ v (x + (s * h) • EuclideanSpace.single i 1))
            (EuclideanSpace.single i 1)) ^ 2 =
          Ω.indicator
            (fun y => ((fderiv ℝ v y) (EuclideanSpace.single i 1)) ^ 2)
            (x + (s * h) • EuclideanSpace.single i 1) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall ?_
    intro s hs
    have hin : x + (s * h) • EuclideanSpace.single i 1 ∈ Ω :=
      h_admissible x hx s hs
    rw [Set.indicator_of_mem hin]
  have heq :
      ∫ s in Set.Ioc (0 : ℝ) 1,
        ((fderiv ℝ v (x + (s * h) • EuclideanSpace.single i 1))
          (EuclideanSpace.single i 1)) ^ 2 =
      ∫ s in Set.Ioc (0 : ℝ) 1,
        Ω.indicator
          (fun y => ((fderiv ℝ v y) (EuclideanSpace.single i 1)) ^ 2)
          (x + (s * h) • EuclideanSpace.single i 1) := by
    refine integral_congr_ae ?_
    exact hpt
  rw [← heq]
  exact hbase

omit [NeZero d] in
theorem lintegral_enorm_sq_diffQuot_le_lintegral_enorm_sq_partialDeriv
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (i : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∫⁻ x : E, (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E) ≤
      ∫⁻ y : E,
        (‖(fderiv ℝ v y) (EuclideanSpace.single i 1)‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure E) := by
  set e : E := EuclideanSpace.single i (1 : ℝ) with he
  set H : E → ℝ≥0∞ := fun y => (‖(fderiv ℝ v y) e‖ₑ : ℝ≥0∞) ^ 2 with hH_def
  have hfd_cont : Continuous (fun y : E => fderiv ℝ v y) :=
    hv.continuous_fderiv one_ne_zero
  have h_partial_cont : Continuous (fun y : E => (fderiv ℝ v y) e) :=
    hfd_cont.clm_apply continuous_const
  have hH_meas : Measurable H := by
    rw [hH_def]
    exact h_partial_cont.measurable.enorm.pow_const 2
  have hPair_meas :
      Measurable (fun p : E × ℝ => H (p.1 + (p.2 * h) • e)) := by
    have h1 : Measurable (fun p : E × ℝ => p.1) := measurable_fst
    have h2 : Measurable (fun p : E × ℝ => p.2) := measurable_snd
    have h3 : Measurable (fun p : E × ℝ => p.2 * h) :=
      h2.mul measurable_const
    have h4 : Measurable (fun p : E × ℝ => (p.2 * h) • e) :=
      h3.smul measurable_const
    have h5 : Measurable (fun p : E × ℝ => p.1 + (p.2 * h) • e) :=
      h1.add h4
    exact hH_meas.comp h5
  have hpt : ∀ x : E,
      (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ 2 ≤
        ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) := by
    intro x
    have hreal := sq_diffQuot_le_integral_sq_partialDeriv (d := d) hv i hh x
    have hLHS_eq :
        (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ 2 =
          ENNReal.ofReal ((diffQuot i h v x) ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have hgamma_cont : Continuous (fun s : ℝ => x + (s * h) • e) :=
      continuous_const.add
        ((continuous_id.mul continuous_const).smul continuous_const)
    have hreal_int_cont : Continuous (fun s : ℝ =>
        ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) :=
      ((h_partial_cont.comp hgamma_cont)).pow 2
    have hreal_int :
        Integrable (fun s : ℝ => ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
      hreal_int_cont.integrableOn_Ioc (a := 0) (b := 1)
    have hConvert :
        ENNReal.ofReal
            (∫ s in Set.Ioc (0 : ℝ) 1,
              ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) := by
      rw [ofReal_integral_eq_lintegral_ofReal hreal_int
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
      refine lintegral_congr_ae ?_
      filter_upwards with s
      change ENNReal.ofReal (((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
        (‖(fderiv ℝ v (x + (s * h) • e)) e‖ₑ : ℝ≥0∞) ^ 2
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [hLHS_eq, ← hConvert]
    exact ENNReal.ofReal_le_ofReal hreal
  have h_step12 :
      ∫⁻ x : E, (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E) ≤
        ∫⁻ x : E,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e))
          ∂(volume : Measure E) := by
    refine lintegral_mono ?_
    intro x; exact hpt x
  have hAEMeas_pair : AEMeasurable
      (Function.uncurry (fun (x : E) (s : ℝ) => H (x + (s * h) • e)))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    have : Measurable (Function.uncurry
        (fun (x : E) (s : ℝ) => H (x + (s * h) • e))) := hPair_meas
    exact this
  have h_swap :
      ∫⁻ x : E,
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ∫⁻ x : E, H (x + (s * h) • e) := by
    exact lintegral_lintegral_swap hPair_meas.aemeasurable
  have hTrans : ∀ s : ℝ,
      ∫⁻ x : E, H (x + (s * h) • e) ∂(volume : Measure E) =
        ∫⁻ y : E, H y ∂(volume : Measure E) := by
    intro s
    have hMP : MeasurePreserving
        (fun x : E => x + (s * h) • e) volume volume :=
      measurePreserving_add_right volume _
    exact hMP.lintegral_comp hH_meas
  have h_inner_eq :
      (fun s : ℝ => ∫⁻ x : E, H (x + (s * h) • e) ∂(volume : Measure E)) =
        fun _ => ∫⁻ y : E, H y ∂(volume : Measure E) := by
    funext s; exact hTrans s
  have hVol_unit : ((volume : Measure ℝ)) (Set.Ioc (0 : ℝ) 1) = 1 := by
    simp [Real.volume_Ioc]
  have h_lintegral_const :
      ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ∫⁻ x : E, H (x + (s * h) • e) ∂(volume : Measure E)
        ∂((volume : Measure ℝ)) = ∫⁻ y : E, H y ∂(volume : Measure E) := by
    rw [h_inner_eq]
    rw [lintegral_const]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [hVol_unit]
  calc ∫⁻ x : E, (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E)
      ≤ ∫⁻ x : E,
            (∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e))
            ∂(volume : Measure E) := h_step12
    _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ x : E, H (x + (s * h) • e)
            ∂(volume : Measure E)
          ∂((volume : Measure ℝ)) := h_swap
    _ = ∫⁻ y : E, H y ∂(volume : Measure E) := h_lintegral_const

omit [NeZero d] in
theorem eLpNorm_diffQuot_le_eLpNorm_partialDeriv
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (i : Fin d) {h : ℝ} (hh : h ≠ 0) :
    eLpNorm (diffQuot i h v) 2 (volume : Measure E) ≤
      eLpNorm (fun y =>
        (fderiv ℝ v y) (EuclideanSpace.single i 1)) 2 (volume : Measure E) := by
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
    show ENNReal.toReal 2 = 2
    rfl
  rw [h2_toReal]
  have h_pow_eq :
      ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  conv_lhs =>
    rw [show
        (∫⁻ x : E, (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure E)) =
          ∫⁻ x : E, (‖diffQuot i h v x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure E) from by
        refine lintegral_congr_ae ?_
        filter_upwards with x using h_pow_eq _]
  conv_rhs =>
    rw [show
        (∫⁻ y : E, (‖(fderiv ℝ v y) (EuclideanSpace.single i 1)‖ₑ : ℝ≥0∞) ^
              (2 : ℝ)
            ∂(volume : Measure E)) =
          ∫⁻ y : E,
              (‖(fderiv ℝ v y) (EuclideanSpace.single i 1)‖ₑ : ℝ≥0∞) ^
                (2 : ℕ)
              ∂(volume : Measure E) from by
        refine lintegral_congr_ae ?_
        filter_upwards with y using h_pow_eq _]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact lintegral_enorm_sq_diffQuot_le_lintegral_enorm_sq_partialDeriv
    (d := d) hv i hh

omit [NeZero d] in
private lemma diffQuot_bound_of_lipschitz
    {φ : E → ℝ} (hφ_C1 : ContDiff ℝ 1 φ) (hφ_supp : HasCompactSupport φ)
    (i : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℝ, ∀ x : E, |diffQuot i h φ x| ≤ L := by
  obtain ⟨L, hL_nn, hLip⟩ :=
    lipschitz_of_contDiff_compactSupport (d := d) hφ_C1 hφ_supp
  refine ⟨L, hL_nn, fun h x => ?_⟩
  by_cases hh : h = 0
  · rw [hh, diffQuot_zero_h]; simpa using hL_nn
  · rw [diffQuot_apply_of_ne (d := d) i hh φ x]
    have hLip_apply :
        ‖φ (x + h • EuclideanSpace.single i 1) - φ x‖ ≤
          L * ‖x + h • EuclideanSpace.single i 1 - x‖ := hLip _ _
    have hsimp : x + h • EuclideanSpace.single i 1 - x =
        h • EuclideanSpace.single i 1 := by
      rw [add_sub_cancel_left]
    rw [hsimp] at hLip_apply
    have hsing_norm :
        ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ = 1 := by simp
    have hnorm_smul :
        ‖h • EuclideanSpace.single i (1 : ℝ)‖ = |h| := by
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    rw [hnorm_smul] at hLip_apply
    rw [abs_div]
    have habs_h : 0 < |h| := abs_pos.mpr hh
    rw [div_le_iff₀ habs_h]
    have h_lhs_norm :
        |φ (x + h • EuclideanSpace.single i 1) - φ x| =
          ‖φ (x + h • EuclideanSpace.single i 1) - φ x‖ :=
      (Real.norm_eq_abs _).symm
    rw [h_lhs_norm]
    exact hLip_apply

end Poincare.Analysis.Sobolev
