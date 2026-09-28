import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Coarea
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.AreaScaleEstimates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}

theorem integral_regularLevel_sectionalError_le_with_scale
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hn : 2 ≤ n) (hα : 0 < α) (hslab : Icc a b ⊆ I)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (harea : ∀ t ∈ Icc a b, g.regularLevelArea hf t ≤ α * t ^ n)
    (hhess : ∀ t ∈ Icc a b, ∀ x, f x = t →
      ∀ v : TangentSpace (𝓡 (n + 1)) x,
        g.inner x (D.gradient f x) v = 0 →
        D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v)
    (hspeed : ∀ x ∈ f ⁻¹' Icc a b,
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    (∫ t in Icc a b, 1 + ∫ z,
      D.levelSectionalError f K (α / t) (openLevelIncl f (g.regularDomain hf) t z)
      ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) ≤
      (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
        ((b - a) + ((n : ℝ) * (1 + α) * α ^ 3 + α ^ 2) * b ^ (n - 1)) := by
  let U := g.regularDomain hf
  let A := g.regularLevelArea hf
  let J := fun t => ∫ z, K (openLevelIncl f U t z)
    ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t
  let N := fun t => ∫ z, max 0 (-D.levelMeanCurvature f (openLevelIncl f U t z))
    ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t
  let E := fun t => ∫ z, D.levelSectionalError f K (α / t) (openLevelIncl f U t z)
    ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t
  have hc := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  have hU : f ⁻¹' Icc a b ⊆ U := fun x hx =>
    (g.mem_regularDomain_iff hf x).mpr (hreg x (hslab hx))
  have hJc : ContinuousOn J (Icc a b) :=
    g.continuousOn_regularLevelIntegral_compact_slab hf U
      (g.regularDomain_regular hf) hc hU hKc
  have hNc : ContinuousOn N (Icc a b) :=
    g.continuousOn_regularLevelIntegral_compact_slab hf U
      (g.regularDomain_regular hf) hc hU
      ((continuousOn_const (c := (0 : ℝ))).sup
        (D.continuousOn_levelMeanCurvature_regularDomain hf).neg)
  have hAs := (D.first_variation_regularLevelArea hf hI hproper hreg).1
  have hAc : ContinuousOn A (Icc a b) := hAs.continuousOn.mono hslab
  have hDc : ContinuousOn (deriv A) (Icc a b) :=
    (hAs.continuousOn_deriv_of_isOpen hI (by simp)).mono hslab
  have hβc : ContinuousOn (fun t : ℝ => α / t) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')
  have hEc : ContinuousOn E (Icc a b) := by
    apply (hJc.add ((hNc.add ((hβc.const_mul n).mul hAc)).mul hβc)).congr
    intro t ht
    exact D.integral_levelSectionalError_eq hf hI hproper hreg (hslab ht) hKc (α / t)
  have hWi := (hAc.mul (hβc.pow 2)).integrableOn_compact isCompact_Icc
    (μ := volume)
  have hDi := (hDc.mul hβc).integrableOn_compact isCompact_Icc (μ := volume)
  have hJi := hJc.integrableOn_compact isCompact_Icc (μ := volume)
  have hEi := hEc.integrableOn_compact isCompact_Icc (μ := volume)
  have hi1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a b) volume :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      1 + E t ≤ J t + (1 + (n : ℝ) * (1 + α) * (A t * (α / t) ^ 2) -
        deriv A t * (α / t)) := by
    have h := D.integral_levelSectionalError_le hf hI hproper hreg (hslab ht)
      hα (div_nonneg hα.le (ha.trans_le ht.1).le) hKc (hhess t ht)
      (fun x hx => hspeed x (by change f x ∈ Icc a b; rwa [hx]))
    change E t ≤ J t + (n : ℝ) * (1 + α) * (α / t) ^ 2 * A t -
      (α / t) * deriv A t at h
    nlinarith only [h]
  have hbound := setIntegral_mono_on (hi1.add hEi)
    (hJi.add ((hi1.add (hWi.const_mul ((n : ℝ) * (1 + α)))).sub hDi))
    measurableSet_Icc hpoint
  have hareaErr := Poincare.CurvatureIntegral.area_error_le_mul_pow
    ha hab hn hα.le hAc
    ((hAs.differentiableOn (by simp)).mono (Ioo_subset_Icc_self.trans hslab))
    (by apply ContinuousOn.intervalIntegrable; rwa [uIcc_of_le hab])
    (fun t ht => ⟨g.regularLevelArea_nonneg hf t, harea t ht⟩)
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hareaErr
  have hKbound : (∫ t in Icc a b, J t) ≤ ∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure := by
    let s := fun x => g.tangentNorm x (g.gradient f x)
    have hsc : Continuous s := g.continuous_tangentNorm_gradient hf
    have heq := g.integral_coarea_compact_slab hf U (g.regularDomain_regular hf)
      hc hU (hKc.mul hsc.continuousOn)
    dsimp only [Pi.mul_apply] at heq
    have hEq : (∫ x in f ⁻¹' Icc a b, K x * s x ∂g.volumeMeasure) = ∫ t in Icc a b, J t := by
      rw [heq]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      apply integral_congr_ae
      filter_upwards [] with z
      exact mul_div_cancel_right₀ _ (ne_of_gt z.1.2)
    rw [← hEq]
    exact setIntegral_mono_on ((hKc.mul hsc.continuousOn).mono hU |>.integrableOn_compact hc)
      ((hKc.mono hU).integrableOn_compact hc)
      (isClosed_Icc.preimage hf.continuous).measurableSet
      (fun x hx => by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hspeed x hx).2 (hK x hx))
  change (∫ t in Icc a b, 1 + E t) ≤ _ at hbound ⊢
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] at hbound
  change IntegrableOn (fun t => A t * (α / t) ^ 2) (Icc a b) volume at hWi
  change IntegrableOn (fun t => deriv A t * (α / t)) (Icc a b) volume at hDi
  have hiP : IntegrableOn (fun t => 1 + (n : ℝ) * (1 + α) *
      (A t * (α / t) ^ 2)) (Icc a b) volume :=
    hi1.add (hWi.const_mul ((n : ℝ) * (1 + α)))
  have hiR : IntegrableOn (fun t => 1 + (n : ℝ) * (1 + α) *
      (A t * (α / t) ^ 2) - deriv A t * (α / t)) (Icc a b) volume := hiP.sub hDi
  rw [integral_add hJi hiR, integral_sub hiP hDi,
    integral_add hi1 (hWi.const_mul ((n : ℝ) * (1 + α))), integral_const_mul,
    integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
    ← Measure.real, Real.volume_real_Icc_of_le hab] at hbound
  linarith only [hbound, hareaErr, hKbound]

theorem integral_regularLevel_sectionalError_le_of_power_bound
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hn : 2 ≤ n) (hα : 0 < α) (hslab : Icc a b ⊆ I)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (harea : ∀ t ∈ Icc a b, g.regularLevelArea hf t ≤ α * t ^ n)
    (hhess : ∀ t ∈ Icc a b, ∀ x, f x = t →
      ∀ v : TangentSpace (𝓡 (n + 1)) x,
        g.inner x (D.gradient f x) v = 0 →
        D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v)
    (hspeed : ∀ x ∈ f ⁻¹' Icc a b,
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    (∫ t in Icc a b, 1 + ∫ z,
      D.levelSectionalError f K (α / t) (openLevelIncl f (g.regularDomain hf) t z)
      ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) ≤
      (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
        (1 + (n : ℝ) * (1 + α) * α ^ 3 + α ^ 2) := by
  have h := D.integral_regularLevel_sectionalError_le_with_scale hf hI hproper hreg
    ha hab hn hα hslab hKc hK harea hhess hspeed
  have hp : b ^ (n - 1) ≤ 1 := pow_le_one₀ (ha.trans_le hab).le hb
  have hcoef : 0 ≤ (n : ℝ) * (1 + α) * α ^ 3 + α ^ 2 := by positivity
  have hscale := mul_le_mul_of_nonneg_left hp hcoef
  linarith only [h, hscale, ha, hb]

end PoincareConjecture.LeviCivitaData
