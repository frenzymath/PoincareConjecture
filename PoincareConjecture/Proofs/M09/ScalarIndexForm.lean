import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture.Proofs.M09

noncomputable def scalarIndexDensity (B C f : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv f s ^ 2 + B s * f s * deriv f s + C s * f s ^ 2

noncomputable def scalarMixedIndexDensity (B C f g : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv f s * deriv g s + B s / 2 * (deriv f s * g s + f s * deriv g s) +
    C s * f s * g s

noncomputable def scalarIndex (B C : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ s in 0..c, scalarIndexDensity B C f s

noncomputable def scalarMixedIndex (B C : ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ s in 0..c, scalarMixedIndexDensity B C f g s

theorem scalarIndexDensity_continuousOn (B C f : ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (hf : ContDiffOn ℝ ∞ f U) : ContinuousOn (scalarIndexDensity B C f) U := by
  have hd := (hf.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  exact ((hd.pow 2).add ((hB.mul hf.continuousOn).mul hd)).add
    (hC.mul (hf.continuousOn.pow 2))

theorem scalarMixedIndexDensity_continuousOn (B C f g : ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContinuousOn (scalarMixedIndexDensity B C f g) U := by
  have hdf := (hf.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  have hdg := (hg.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  exact ((hdf.mul hdg).add ((hB.div_const 2).mul
    ((hdf.mul hg.continuousOn).add (hf.continuousOn.mul hdg)))).add
      ((hC.mul hf.continuousOn).mul hg.continuousOn)

theorem scalarIndex_add_mul (B C f g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (t : ℝ) :
    scalarIndex B C c (fun s ↦ f s + t * g s) = scalarIndex B C c f +
      (2 * t) * scalarMixedIndex B C c f g + t ^ 2 * scalarIndex B C c g := by
  have hfi : IntervalIntegrable (scalarIndexDensity B C f) MeasureTheory.volume 0 c :=
    ((scalarIndexDensity_continuousOn B C f U hU hB hC hf).mono hKU).intervalIntegrable_of_Icc hc
  have hgi : IntervalIntegrable (scalarIndexDensity B C g) MeasureTheory.volume 0 c :=
    ((scalarIndexDensity_continuousOn B C g U hU hB hC hg).mono hKU).intervalIntegrable_of_Icc hc
  have hmi : IntervalIntegrable (scalarMixedIndexDensity B C f g) MeasureTheory.volume 0 c :=
    ((scalarMixedIndexDensity_continuousOn B C f g U hU hB hC hf hg).mono hKU).intervalIntegrable_of_Icc hc
  unfold scalarIndex scalarMixedIndex
  calc
    (∫ s in 0..c, scalarIndexDensity B C (fun r ↦ f r + t * g r) s) =
        ∫ s in 0..c, scalarIndexDensity B C f s +
          (2 * t) * scalarMixedIndexDensity B C f g s + t ^ 2 * scalarIndexDensity B C g s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsU := hKU (by simpa only [Set.uIcc_of_le hc] using hs)
      have hfd := ((hf.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)).hasDerivAt
      have hgd := ((hg.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)).hasDerivAt
      have hd : deriv (fun r ↦ f r + t * g r) s = deriv f s + t * deriv g s := by
        simpa only [Pi.add_def] using (hfd.add (hgd.const_mul t)).deriv
      dsimp only [scalarIndexDensity, scalarMixedIndexDensity]
      rw [hd]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hfi.add (hmi.const_mul _)) (hgi.const_mul _),
        intervalIntegral.integral_add hfi (hmi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

set_option backward.isDefEq.respectTransparency false in
theorem linear_coefficient_of_nonneg_quadratic (a b : ℝ)
    (h : ∀ t : ℝ, 0 ≤ a * t + b * t ^ 2) : a = 0 := by
  have hmin : IsLocalMin (fun t : ℝ ↦ a * t + b * t ^ 2) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using h t
  have hd : HasDerivAt (fun t : ℝ ↦ a * t + b * t ^ 2) a 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul a).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul b) using 1 <;> norm_num
  exact hmin.hasDerivAt_eq_zero hd

theorem scalarIndex_stationary (B C : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 c ⊆ U)
    (hB : ContinuousOn B U) (hC : ContinuousOn C U) (d : ℝ)
    (hcompare : ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U → f 0 = 0 →
      d * f c ^ 2 ≤ scalarIndex B C c f)
    (heq : scalarIndex B C c (fun s ↦ s / c) = d)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hw0 : w 0 = 0) :
    scalarMixedIndex B C c (fun s ↦ s / c) w = d * w c := by
  have hy : ContDiffOn ℝ ∞ (fun s : ℝ ↦ s / c) U := contDiffOn_id.div_const c
  have hq (t : ℝ) :
      0 ≤ (2 * (scalarMixedIndex B C c (fun s ↦ s / c) w - d * w c)) * t +
        (scalarIndex B C c w - d * w c ^ 2) * t ^ 2 := by
    have h := hcompare (fun s ↦ s / c + t * w s)
      (hy.add (contDiffOn_const.mul hw)) (by simp [hw0])
    rw [scalarIndex_add_mul B C _ w c hc.le U hU hKU hB hC hy hw t, heq] at h
    have hcc : c / c = 1 := div_self hc.ne'
    rw [hcc] at h
    nlinarith
  have h := linear_coefficient_of_nonneg_quadratic _ _ hq
  linarith

end PoincareConjecture.Proofs.M09
