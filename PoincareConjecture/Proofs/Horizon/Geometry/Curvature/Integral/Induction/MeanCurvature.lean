import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Area








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  {I : Set ℝ} (hI : IsOpen I)
  (hproper : IsProperMap (I.restrictPreimage f))
  (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

include hI hproper hreg in


theorem integrable_regularLevelVolume_of_isProperMap
    {t : ℝ} (ht : t ∈ I) {h : M → ℝ}
    (hh : ContinuousOn h (g.regularDomain hf)) :
    Integrable (h ∘ openLevelIncl f (g.regularDomain hf) t)
      (g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) := by
  let := isFiniteMeasure_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ht
  have hlevel : IsCompact (f ⁻¹' {t}) := by
    simpa only [Icc_self] using Poincare.Coarea.isCompact_slab_of_isProperMap hproper
      (show Icc t t ⊆ I by simpa only [Icc_self, singleton_subset_iff] using ht)
  have hU : f ⁻¹' {t} ⊆ g.regularDomain hf := by
    intro x hx
    apply (g.mem_regularDomain_iff hf x).mpr
    apply hreg
    rw [show f x = t from hx]
    exact ht
  have hc : IsCompact (univ : Set (openLevelSet f (g.regularDomain hf) t)) := by
    apply (isEmbedding_openLevelIncl f (g.regularDomain hf) t).isCompact_iff.mpr
    rw [image_univ, range_openLevelIncl, inter_eq_right.mpr hU]
    exact hlevel
  have hh' : Continuous (h ∘ openLevelIncl f (g.regularDomain hf) t) :=
    hh.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => z.1.2)
  simpa only [integrableOn_univ] using hh'.continuousOn.integrableOn_compact hc

variable (D : LeviCivitaData g)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
theorem continuousOn_levelMeanCurvature_regularDomain :
    ContinuousOn (D.levelMeanCurvature f) (g.regularDomain hf) := by
  apply (D.continuousOn_levelMeanCurvature hf).mono
  intro x hx
  exact Real.sqrt_pos.mp hx

include hI hproper hreg in

theorem integral_pos_levelMeanCurvature_le
    {t β : ℝ} (ht : t ∈ I) (hβ : 0 ≤ β)
    (hH : ∀ x, f x = t → D.levelMeanCurvature f x ≤ (n : ℝ) * β) :
    (∫ z, max 0 (D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z))
      ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) ≤
        (n : ℝ) * β * g.regularLevelArea hf t := by
  let := isFiniteMeasure_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ht
  have hi := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht
    ((continuousOn_const (c := (0 : ℝ))).sup
      (D.continuousOn_levelMeanCurvature_regularDomain hf))
  dsimp only [Function.comp_def] at hi
  have hbound : ∀ z : openLevelSet f (g.regularDomain hf) t,
      max 0 (D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z)) ≤
        (n : ℝ) * β := by
    intro z
    exact max_le (mul_nonneg (Nat.cast_nonneg n) hβ) (hH _ z.2)
  have hi' := integral_mono hi (integrable_const ((n : ℝ) * β)) hbound
  simpa only [integral_const, smul_eq_mul, RiemannianMetric.regularLevelArea,
    mul_comm _ ((n : ℝ) * β)] using hi'

private theorem neg_part_le_scaled_upper_sub_div
    {H s B α : ℝ} (hB : 0 ≤ B) (hα : 0 < α) (hH : H ≤ B)
    (hslow : 1 / α ≤ s) (hsup : s ≤ 1) :
    max 0 (-H) ≤ B * α - H / s := by
  have hs : 0 < s := (one_div_pos.mpr hα).trans_le hslow
  by_cases hH0 : 0 ≤ H
  · rw [max_eq_left (neg_nonpos.mpr hH0)]
    have hinv : s⁻¹ ≤ α := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hs).mpr
      have h := (div_le_iff₀ hα).mp hslow
      nlinarith
    have hquot : H / s ≤ B * α := by
      calc
        H / s = H * s⁻¹ := div_eq_mul_inv _ _
        _ ≤ H * α := mul_le_mul_of_nonneg_left hinv hH0
        _ ≤ B * α := mul_le_mul_of_nonneg_right hH hα.le
    linarith
  · have hH0' : H ≤ 0 := le_of_not_ge hH0
    rw [max_eq_right (neg_nonneg.mpr hH0')]
    have hquot : H / s ≤ H := (div_le_iff₀ hs).mpr (by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left hsup hH0')
    have hBa : 0 ≤ B * α := mul_nonneg hB hα.le
    linarith

include hI hproper hreg in


theorem integral_neg_levelMeanCurvature_le_sub_deriv
    {t α β : ℝ} (ht : t ∈ I) (hα : 0 < α) (hβ : 0 ≤ β)
    (hH : ∀ x, f x = t → D.levelMeanCurvature f x ≤ (n : ℝ) * β)
    (hspeed : ∀ x, f x = t →
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    (∫ z, max 0 (-D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z))
      ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) ≤
        (n : ℝ) * α * β * g.regularLevelArea hf t - deriv (g.regularLevelArea hf) t := by
  let := isFiniteMeasure_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ht
  have hHc := D.continuousOn_levelMeanCurvature_regularDomain hf
  have hi := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht
    ((continuousOn_const (c := (0 : ℝ))).sup hHc.neg)
  have hquot := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht
    (hHc.div (g.continuous_tangentNorm_gradient hf).continuousOn
      (fun x hx => ne_of_gt hx))
  dsimp only [Function.comp_def, Pi.neg_apply, Pi.div_apply] at hi hquot
  have hbound : ∀ z : openLevelSet f (g.regularDomain hf) t,
      max 0 (-D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z)) ≤
        (n : ℝ) * α * β -
          D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z) /
            g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
              (g.gradient f (openLevelIncl f (g.regularDomain hf) t z)) := by
    intro z
    have hs := hspeed _ z.2
    have h := neg_part_le_scaled_upper_sub_div (mul_nonneg (Nat.cast_nonneg n) hβ)
      hα (hH _ z.2) hs.1 hs.2
    simpa only [openLevelIncl, mul_right_comm (n : ℝ) β α] using h
  have hi' := integral_mono hi ((integrable_const ((n : ℝ) * α * β)).sub hquot) hbound
  dsimp only [Pi.sub_apply] at hi'
  rw [integral_sub (integrable_const _) hquot, integral_const,
    ← ((D.first_variation_regularLevelArea hf hI hproper hreg).2 t ht).deriv] at hi'
  simpa only [smul_eq_mul, RiemannianMetric.regularLevelArea,
    mul_comm _ ((n : ℝ) * α * β)] using hi'

end PoincareConjecture.LeviCivitaData
