import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Producer
import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.UniformMollification
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U V K : Set (Spacetime n)}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem tendstoUniformly_lebesgueConvolution
    {u : Spacetime n → ℝ} (hu : UniformContinuous u)
    {ρ : ℕ → ContDiffBump (0 : Spacetime n)}
    (hρ : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0)) :
    TendstoUniformly
      (fun k => lebesgueConvolution ((ρ k).normed volume) u) u atTop := by
  simpa only [lebesgueConvolution_eq_convolution] using
    (Poincare.Analysis.Convolution.tendstoUniformly_normed_convolution
      volume hu hρ)

theorem tendstoUniformlyOn_lebesgueConvolution
    {u : Spacetime n → ℝ} (hu : UniformContinuous u)
    {ρ : ℕ → ContDiffBump (0 : Spacetime n)}
    (hρ : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0))
    (K : Set (Spacetime n)) :
    TendstoUniformlyOn
      (fun k => lebesgueConvolution ((ρ k).normed volume) u) u atTop K :=
  (tendstoUniformly_lebesgueConvolution hu hρ).tendstoUniformlyOn

theorem tendstoUniformlyOn_lebesgueConvolution_of_eqOn
    {u u' : Spacetime n → ℝ} {V K : Set (Spacetime n)}
    (hu' : UniformContinuous u') (hVK : V ⊆ K) (hEq : EqOn u' u K)
    {ρ : ℕ → ContDiffBump (0 : Spacetime n)}
    (hρ : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0))
    (hs : ∀ᶠ k in atTop, ∀ z ∈ V,
      tsupport (translatedKernel ((ρ k).normed volume) z) ⊆ K) :
    TendstoUniformlyOn
      (fun k => lebesgueConvolution ((ρ k).normed volume) u) u atTop V := by
  have hglobal := tendstoUniformlyOn_lebesgueConvolution hu' hρ (K := V)
  refine (Metric.tendstoUniformlyOn_iff.mpr ?_)
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hglobal) ε hε, hs] with k hk hsk z hz
  have hconv : lebesgueConvolution ((ρ k).normed volume) u z =
      lebesgueConvolution ((ρ k).normed volume) u' z := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ K
    · rw [hEq hy]
    · have hzero : translatedKernel ((ρ k).normed volume) z y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy (hsk z hz h))
      simp only [translatedKernel] at hzero
      simp [hzero]
  have hval : u' z = u z := hEq (hVK hz)
  rw [hconv, ← hval]
  exact hk z hz

theorem tendstoUniformly_lebesgueConvolution_of_continuous_compactSupport
    {u : Spacetime n → ℝ} (hu : Continuous u) (huc : HasCompactSupport u)
    {ρ : ℕ → ContDiffBump (0 : Spacetime n)}
    (hρ : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0)) :
    TendstoUniformly
      (fun k => lebesgueConvolution ((ρ k).normed volume) u) u atTop :=
  (tendstoUniformlyOn_univ.mp (tendstoUniformlyOn_lebesgueConvolution_of_eqOn
    (huc.uniformContinuous_of_continuous hu) (subset_rfl : (Set.univ : Set (Spacetime n)) ⊆ Set.univ)
    (fun _ _ => rfl) hρ (Filter.Eventually.of_forall (fun _ _ _ => subset_univ _))))

theorem tendstoUniformlyOn_lebesgueConvolution_of_continuous_compactSupport
    {u : Spacetime n → ℝ} (hu : Continuous u) (huc : HasCompactSupport u)
    {ρ : ℕ → ContDiffBump (0 : Spacetime n)}
    (hρ : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0))
    (K : Set (Spacetime n)) :
    TendstoUniformlyOn
      (fun k => lebesgueConvolution ((ρ k).normed volume) u) u atTop K :=
  (tendstoUniformly_lebesgueConvolution_of_continuous_compactSupport hu huc hρ).tendstoUniformlyOn

private theorem convolution_right_eq (η f : Spacetime n → ℝ) :
    lebesgueConvolution η f = f ⋆[lsmul ℝ ℝ, volume] η := by
  funext z
  simp only [lebesgueConvolution, convolution_def, lsmul_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact mul_comm _ _

theorem contDiff_lebesgueConvolution {η f : Spacetime n → ℝ}
    (hf : LocallyIntegrable f volume) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) : ContDiff ℝ ∞ (lebesgueConvolution η f) := by
  rw [convolution_right_eq]
  exact hηc.contDiff_convolution_right (lsmul ℝ ℝ) hf hη

theorem fderiv_lebesgueConvolution {η f : Spacetime n → ℝ}
    (hf : LocallyIntegrable f volume) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (z v : Spacetime n) :
    fderiv ℝ (lebesgueConvolution η f) z v =
      lebesgueConvolution (fun y => fderiv ℝ η y v) f z := by
  rw [convolution_right_eq,
    (hηc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf (hη.of_le (by simp)) z).fderiv]
  rw [convolution_precompR_apply _ hf (hηc.fderiv ℝ)
    (hη.continuous_fderiv (by simp))]
  simp only [convolution_def, lsmul_apply, smul_eq_mul, lebesgueConvolution]
  apply integral_congr_ae
  filter_upwards [] with y
  exact mul_comm _ _

private theorem smooth_directional {f : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : Spacetime n) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem integrable_mul_supported {f g : Spacetime n → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f g).trans (subset_tsupport g))).mp
  exact ((hf.mul hg).mono hgU).integrableOn_compact hgc

private theorem convolution_indicator_eq {η u : Spacetime n → ℝ}
    {z : Spacetime n} (hs : tsupport (translatedKernel η z) ⊆ K) :
    lebesgueConvolution η (K.indicator u) z = lebesgueConvolution η u z := by
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ K
  · rw [indicator_of_mem hy]
  · have he : η (z - y) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := translatedKernel η z) (fun h => hy (hs h))
    simp [he]

theorem contDiffOn_lebesgueConvolution {η u : Spacetime n → ℝ}
    (hV : IsOpen V) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K) :
    ContDiffOn ℝ ∞ (lebesgueConvolution η u) V := by
  have hi : Integrable (K.indicator u) :=
    (hu.integrableOn_compact hK).integrable_indicator hK.measurableSet
  exact (contDiff_lebesgueConvolution hi.locallyIntegrable hη hηc).contDiffOn.congr
    (fun z hz => (convolution_indicator_eq (hs z hz)).symm)

private theorem derivative_translate {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (z y v : Spacetime n) :
    fderiv ℝ (translatedKernel η z) y v = -fderiv ℝ η (z - y) v := by
  have hd := (hη.differentiable (by simp) (z - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
  change HasFDerivAt (translatedKernel η z) _ y at hd
  rw [hd.fderiv]
  simp

private theorem second_derivative_translate {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (z y v w : Spacetime n) :
    fderiv ℝ (fun x => fderiv ℝ (translatedKernel η z) x v) y w =
      fderiv ℝ (fun x => fderiv ℝ η x v) (z - y) w := by
  have he : (fun x => fderiv ℝ (translatedKernel η z) x v) =
      fun x => -translatedKernel (fun t => fderiv ℝ η t v) z x := by
    funext x
    exact derivative_translate hη z x v
  rw [he]
  change fderiv ℝ (-(translatedKernel (fun t => fderiv ℝ η t v) z)) y w = _
  rw [fderiv_neg]
  simp only [neg_apply, derivative_translate (smooth_directional hη v), neg_neg]

private theorem second_directional_comm {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η) (y v w : Spacetime n) :
    fderiv ℝ (fun x => fderiv ℝ η x v) y w =
      fderiv ℝ (fun x => fderiv ℝ η x w) y v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ η) y :=
    (hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiable (by simp) y
  have he (v w : Spacetime n) :
      fderiv ℝ (fun x => fderiv ℝ η x v) y w = fderiv ℝ (fderiv ℝ η) y w v := by
    simpa using congrArg (fun T : Spacetime n →L[ℝ] ℝ => T w)
      (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).fderiv
  rw [he, he]
  exact hη.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) w v

private theorem translated_support_mono {η κ : Spacetime n → ℝ}
    (hs : tsupport κ ⊆ tsupport η) (z : Spacetime n) :
    tsupport (translatedKernel κ z) ⊆ tsupport (translatedKernel η z) := by
  change tsupport (κ ∘ Homeomorph.subLeft z) ⊆ tsupport (η ∘ Homeomorph.subLeft z)
  rw [tsupport_comp_eq_preimage, tsupport_comp_eq_preimage]
  exact preimage_mono hs

theorem fderiv_lebesgueConvolution_on {η u : Spacetime n → ℝ}
    (hV : IsOpen V) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K)
    {z : Spacetime n} (hz : z ∈ V) (v : Spacetime n) :
    fderiv ℝ (lebesgueConvolution η u) z v =
      lebesgueConvolution (fun y => fderiv ℝ η y v) u z := by
  have hi : Integrable (K.indicator u) :=
    (hu.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have he : lebesgueConvolution η u =ᶠ[𝓝 z] lebesgueConvolution η (K.indicator u) := by
    filter_upwards [hV.mem_nhds hz] with w hw
    exact (convolution_indicator_eq (hs w hw)).symm
  rw [he.fderiv_eq, fderiv_lebesgueConvolution hi.locallyIntegrable hη hηc]
  exact convolution_indicator_eq
    ((translated_support_mono (tsupport_fderiv_apply_subset ℝ v) z).trans (hs z hz))

private theorem second_fderiv_lebesgueConvolution_on {η u : Spacetime n → ℝ}
    (hV : IsOpen V) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K)
    {z : Spacetime n} (hz : z ∈ V) (v w : Spacetime n) :
    fderiv ℝ (fun x => fderiv ℝ (lebesgueConvolution η u) x v) z w =
      lebesgueConvolution (fun y => fderiv ℝ (fun x => fderiv ℝ η x v) y w) u z := by
  have he : (fun x => fderiv ℝ (lebesgueConvolution η u) x v) =ᶠ[𝓝 z]
      lebesgueConvolution (fun y => fderiv ℝ η y v) u := by
    filter_upwards [hV.mem_nhds hz] with x hx
    exact fderiv_lebesgueConvolution_on hV hK hu hη hηc hs hx v
  rw [he.fderiv_eq]
  exact fderiv_lebesgueConvolution_on hV hK hu (smooth_directional hη v)
    (hηc.fderiv_apply ℝ v)
    (fun x hx => (translated_support_mono (tsupport_fderiv_apply_subset ℝ v) x).trans
      (hs x hx)) hz w

private theorem integrable_kernel_mul {η u : Spacetime n → ℝ}
    (hu : ContinuousOn u K) (hη : Continuous η) (hηc : HasCompactSupport η)
    {z : Spacetime n} (hs : tsupport (translatedKernel η z) ⊆ K) :
    Integrable (fun y => η (z - y) * u y) := by
  simpa only [mul_comm, Function.comp_def, Pi.sub_apply, id_eq] using integrable_mul_supported hu
    ((hη.comp (continuous_const.sub continuous_id)).continuousOn)
    (hηc.comp_homeomorph (Homeomorph.subLeft z)) hs

private theorem operator_lebesgueConvolution_eq_integral
    (C : Coefficients n) {η u : Spacetime n → ℝ}
    (hV : IsOpen V) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K)
    {z : Spacetime n} (hz : z ∈ V) :
    C.operator (lebesgueConvolution η u) z =
      ∫ y, u y * (-timeDeriv (translatedKernel η z) y -
        (∑ i, ∑ j, C.principal i j z *
          spatialDeriv j (spatialDeriv i (translatedKernel η z)) y) -
        (∑ i, C.drift i z * spatialDeriv i (translatedKernel η z) y) +
        C.zeroth z * translatedKernel η z y) := by
  have ht := integrable_kernel_mul hu (smooth_directional hη (0, 1)).continuous
    (hηc.fderiv_apply ℝ (0, 1))
    ((translated_support_mono (tsupport_fderiv_apply_subset ℝ (0, 1)) z).trans (hs z hz))
  have ha (i j : Fin n) : Integrable (fun y =>
      C.principal i j z * (spatialDeriv i (spatialDeriv j η) (z - y) * u y)) := by
    apply Integrable.const_mul
    exact integrable_kernel_mul hu
      (smooth_directional (smooth_directional hη (spatialDirection j))
        (spatialDirection i)).continuous
      ((hηc.fderiv_apply ℝ (spatialDirection j)).fderiv_apply ℝ (spatialDirection i))
      ((translated_support_mono ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
        (tsupport_fderiv_apply_subset ℝ (spatialDirection j))) z).trans (hs z hz))
  have hb (i : Fin n) : Integrable (fun y =>
      C.drift i z * (spatialDeriv i η (z - y) * u y)) := by
    apply Integrable.const_mul
    exact integrable_kernel_mul hu (smooth_directional hη (spatialDirection i)).continuous
      (hηc.fderiv_apply ℝ (spatialDirection i))
      ((translated_support_mono (tsupport_fderiv_apply_subset ℝ (spatialDirection i)) z).trans
        (hs z hz))
  have hc := (integrable_kernel_mul hu hη.continuous hηc (hs z hz)).const_mul (C.zeroth z)
  have hsa := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => ha i j))
  have hsb := integrable_finsetSum Finset.univ (fun i _ => hb i)
  have hleft : C.operator (lebesgueConvolution η u) z =
      (∫ y, timeDeriv η (z - y) * u y) -
      (∑ i, ∑ j, ∫ y, C.principal i j z * (spatialDeriv i (spatialDeriv j η) (z-y) * u y)) +
      (∑ i, ∫ y, C.drift i z * (spatialDeriv i η (z-y) * u y)) +
      ∫ y, C.zeroth z * (η (z-y) * u y) := by
    have hd2 (i j : Fin n) :
        spatialDeriv i (spatialDeriv j (lebesgueConvolution η u)) z =
          lebesgueConvolution (spatialDeriv i (spatialDeriv j η)) u z :=
      second_fderiv_lebesgueConvolution_on hV hK hu hη hηc hs hz
        (spatialDirection j) (spatialDirection i)
    simp only [Coefficients.operator, hd2]
    dsimp only [spatialDeriv, timeDeriv]
    simp only [
      fderiv_lebesgueConvolution_on hV hK hu hη hηc hs hz,
      lebesgueConvolution, integral_const_mul]
    rfl
  rw [hleft]
  calc
    _ = ∫ y, timeDeriv η (z-y) * u y -
        (∑ i, ∑ j, C.principal i j z * (spatialDeriv i (spatialDeriv j η) (z-y) * u y)) +
        (∑ i, C.drift i z * (spatialDeriv i η (z-y) * u y)) +
        C.zeroth z * (η (z-y) * u y) := by
      have h1 := integral_add ((ht.sub hsa).add hsb) hc
      have h2 := integral_add (ht.sub hsa) hsb
      have h3 := integral_sub ht hsa
      dsimp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
      dsimp only [timeDeriv]
      rw [h1, h2, h3, integral_finsetSum _ (fun i _ => hb i),
        integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ha i j))]
      simp_rw [integral_finsetSum _ (fun j _ => ha _ j)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hsecond (i j : Fin n) :
          spatialDeriv j (spatialDeriv i (translatedKernel η z)) y =
            spatialDeriv i (spatialDeriv j η) (z-y) :=
        (second_derivative_translate hη z y (spatialDirection i) (spatialDirection j)).trans
          (second_directional_comm hη (z-y) (spatialDirection i) (spatialDirection j))
      simp only [hsecond]
      simp only [spatialDeriv, timeDeriv, derivative_translate hη,
        translatedKernel, neg_neg, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add,
        mul_add, mul_sub, Finset.mul_sum]
      simp only [mul_comm, mul_left_comm, mul_assoc]

private theorem smooth_supported (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact (hf z (hs hz)).contDiffAt (hU.mem_nhds (hs hz))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

private theorem spatial_sub {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) :
    spatialDeriv i (f - g) = spatialDeriv i f - spatialDeriv i g := by
  funext y
  dsimp only [spatialDeriv, Pi.sub_apply]
  rw [fderiv_sub (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
  rfl

private theorem smooth_spatial {f : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (spatialDeriv i f) :=
  smooth_directional hf (spatialDirection i)

private theorem spatial_const_mul {f : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (r : ℝ) (i : Fin n) :
    spatialDeriv i (fun y => r * f y) = fun y => r * spatialDeriv i f y := by
  funext y
  dsimp only [spatialDeriv]
  rw [fderiv_const_mul (hf.differentiable (by simp) y)]
  rfl

private theorem integrable_adjoint (hU : IsOpen U) (C : Coefficients n)
    (hC : C.IsSmoothOn U) {u φ : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun y => u y * C.adjoint φ y) := by
  have hq (q : Spacetime n → ℝ) (hq : ContDiffOn ℝ ∞ q U) :
      ContDiff ℝ ∞ (fun y => q y * φ y) :=
    smooth_supported hU (hq.mul hφ.contDiffOn) (tsupport_mul_subset_right.trans hφU)
  have hi (g : Spacetime n → ℝ) (hg : ContDiff ℝ ∞ g)
      (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) (v : Spacetime n) :
      Integrable (fun y => u y * fderiv ℝ g y v) :=
    integrable_mul_supported hu (smooth_directional hg v).continuous.continuousOn
      (hgc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hgU)
  have ht := hi φ hφ hφc hφU (0, 1)
  have ha (i j : Fin n) : Integrable (fun y => u y * spatialDeriv j
      (spatialDeriv i (fun w => C.principal i j w * φ w)) y) :=
    hi _ (smooth_directional (hq _ (hC.1 i j)) (spatialDirection i))
      (hφc.mul_left.fderiv_apply ℝ (spatialDirection i))
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
        (tsupport_mul_subset_right.trans hφU)) (spatialDirection j)
  have hb (i : Fin n) : Integrable (fun y => u y *
      spatialDeriv i (fun w => C.drift i w * φ w) y) :=
    hi _ (hq _ (hC.2.1 i)) hφc.mul_left
      (tsupport_mul_subset_right.trans hφU) (spatialDirection i)
  have hc := integrable_mul_supported (hu.mul hC.2.2.continuousOn)
    hφ.continuous.continuousOn hφc hφU
  have hsa := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => ha i j))
  have hsb := integrable_finsetSum Finset.univ (fun i _ => hb i)
  refine (((ht.neg.sub hsa).sub hsb).add hc).congr ?_
  filter_upwards [] with y
  simp only [Coefficients.adjoint, timeDeriv, mul_add, mul_sub, mul_neg,
    Finset.mul_sum, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
  ring

theorem WeakSolutionOn.mollification_commutator
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKU : K ⊆ U)
    {C : Coefficients n} (hC : C.IsSmoothOn U) {u η : Spacetime n → ℝ}
    (hu : ContinuousOn u U) (hw : WeakSolutionOn C u U)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K) :
    ContDiffOn ℝ ∞ (lebesgueConvolution η u) V ∧
      ∀ z ∈ V, C.operator (lebesgueConvolution η u) z =
        ∫ y, u y * ((∑ i, ∑ j, spatialDeriv j (spatialDeriv i
          (fun w => (C.principal i j w - C.principal i j z) * translatedKernel η z w)) y) +
          (∑ i, spatialDeriv i
            (fun w => (C.drift i w - C.drift i z) * translatedKernel η z w) y) +
          (C.zeroth z - C.zeroth y) * translatedKernel η z y) := by
  refine ⟨contDiffOn_lebesgueConvolution hV hK (hu.mono hKU) hη hηc hs, ?_⟩
  intro z hz
  let φ := translatedKernel η z
  have hφ : ContDiff ℝ ∞ φ := hη.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hηc.comp_homeomorph (Homeomorph.subLeft z)
  have hφU : tsupport φ ⊆ U := (hs z hz).trans hKU
  let F : Coefficients n := ⟨fun i j _ => C.principal i j z,
    fun i _ => C.drift i z, fun _ => C.zeroth z⟩
  have hF : F.IsSmoothOn U :=
    ⟨fun _ _ => contDiffOn_const, fun _ => contDiffOn_const, contDiffOn_const⟩
  have hfreeze : C.operator (lebesgueConvolution η u) z =
      ∫ y, u y * F.adjoint φ y := by
    rw [operator_lebesgueConvolution_eq_integral C hV hK (hu.mono hKU) hη hηc hs hz]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [Coefficients.adjoint, F, spatial_const_mul hφ,
      spatial_const_mul (smooth_spatial hφ _)]
    rfl
  have hdiff (q : Spacetime n → ℝ) (hq : ContDiffOn ℝ ∞ q U) (r : ℝ) :
      (fun w => (q w - r) * φ w) = (fun w => q w * φ w) - (fun w => r * φ w) := by
    funext w
    simp only [Pi.sub_apply, sub_mul]
  have hqφ (q : Spacetime n → ℝ) (hq : ContDiffOn ℝ ∞ q U) :
      ContDiff ℝ ∞ (fun w => q w * φ w) :=
    smooth_supported hU (hq.mul hφ.contDiffOn) (tsupport_mul_subset_right.trans hφU)
  have hd1 (q : Spacetime n → ℝ) (hq : ContDiffOn ℝ ∞ q U) (r : ℝ) (i : Fin n) :
      spatialDeriv i (fun w => (q w - r) * φ w) =
        spatialDeriv i (fun w => q w * φ w) - fun w => r * spatialDeriv i φ w := by
    rw [hdiff q hq r, spatial_sub (hqφ q hq) (contDiff_const.mul hφ), spatial_const_mul hφ]
  have hd2 (q : Spacetime n → ℝ) (hq : ContDiffOn ℝ ∞ q U) (r : ℝ) (i j : Fin n) :
      spatialDeriv j (spatialDeriv i (fun w => (q w - r) * φ w)) =
        spatialDeriv j (spatialDeriv i (fun w => q w * φ w)) -
          fun w => r * spatialDeriv j (spatialDeriv i φ) w := by
    rw [hd1 q hq r i, spatial_sub (smooth_spatial (hqφ q hq) i)
      (contDiff_const.mul (smooth_spatial hφ i)),
      spatial_const_mul (smooth_spatial hφ i)]
  have hzero : (∫ y, u y * C.adjoint φ y) = 0 := hw.2 φ hφ hφc hφU
  rw [hfreeze, ← sub_zero (∫ y, u y * F.adjoint φ y), ← hzero,
    ← integral_sub (integrable_adjoint hU F hF hu hφ hφc hφU)
      (integrable_adjoint hU C hC hu hφ hφc hφU)]
  apply integral_congr_ae
  filter_upwards [] with y
  change u y * F.adjoint φ y - u y * C.adjoint φ y = _
  change _ = u y * ((∑ i, ∑ j, spatialDeriv j (spatialDeriv i
    (fun w => (C.principal i j w - C.principal i j z) * φ w)) y) +
    (∑ i, spatialDeriv i (fun w => (C.drift i w - C.drift i z) * φ w) y) +
    (C.zeroth z - C.zeroth y) * φ y)
  simp only [hd2 _ (hC.1 _ _), hd1 _ (hC.2.1 _), Coefficients.adjoint, F,
    spatial_const_mul hφ, spatial_const_mul (smooth_spatial hφ _), Pi.sub_apply,
    Finset.sum_sub_distrib]
  ring

private theorem spatial_mul_rule {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin n) (y : Spacetime n) :
    spatialDeriv i (f * g) y =
      f y * spatialDeriv i g y + g y * spatialDeriv i f y := by
  dsimp only [spatialDeriv]
  rw [fderiv_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem spatial_add_rule {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin n) (y : Spacetime n) :
    spatialDeriv i (f + g) y =
      spatialDeriv i f y + spatialDeriv i g y := by
  dsimp only [spatialDeriv]
  rw [fderiv_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
  simp only [add_apply]

theorem spatial_second_coefficient_difference_expansion
    {q η : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q)
    (hη : ContDiff ℝ ∞ η) {z y : Spacetime n} (i j : Fin n) :
    spatialDeriv j (spatialDeriv i
      (fun w => (q w - q z) * η w)) y =
      (q y - q z) * spatialDeriv j (spatialDeriv i η) y +
      spatialDeriv i η y * spatialDeriv j q y +
      η y * spatialDeriv j (spatialDeriv i q) y +
      spatialDeriv i q y * spatialDeriv j η y := by
  let d : Spacetime n → ℝ := q - (fun _ : Spacetime n => q z)
  have hd : ContDiff ℝ ∞ d := hq.sub contDiff_const
  have hdi : ContDiff ℝ ∞ (spatialDeriv i d) :=
    smooth_directional hd (spatialDirection i)
  have hηi : ContDiff ℝ ∞ (spatialDeriv i η) :=
    smooth_directional hη (spatialDirection i)
  have hfirst : spatialDeriv i (d * η) =
      (fun w => d w * spatialDeriv i η w + η w * spatialDeriv i d w) := by
    funext w
    exact spatial_mul_rule hd hη i w
  have hsecond := spatial_mul_rule hd hηi j y
  have hthird := spatial_mul_rule hη hdi j y
  have hadd := spatial_add_rule (hd.mul hηi) (hη.mul hdi) j y
  have hdi_fun : spatialDeriv i d = spatialDeriv i q := by
    funext w
    change (fderiv ℝ (q - (fun _ : Spacetime n => q z)) w)
        (spatialDirection i) = (fderiv ℝ q w) (spatialDirection i)
    rw [fderiv_sub (hq.differentiable (by simp) w)
      (contDiff_const.differentiable one_ne_zero w)]
    simp
  have hdj_fun : spatialDeriv j d = spatialDeriv j q := by
    funext w
    change (fderiv ℝ (q - (fun _ : Spacetime n => q z)) w)
        (spatialDirection j) = (fderiv ℝ q w) (spatialDirection j)
    rw [fderiv_sub (hq.differentiable (by simp) w)
      (contDiff_const.differentiable one_ne_zero w)]
    simp
  have hdi' := congrFun hdi_fun y
  have hdj' := congrFun hdj_fun y
  have hdij' : spatialDeriv j (spatialDeriv i d) y =
      spatialDeriv j (spatialDeriv i q) y := by
    rw [hdi_fun]
  change spatialDeriv j (spatialDeriv i (d * η)) y = _
  rw [hfirst]
  have hadd' : spatialDeriv j
      (fun w => d w * spatialDeriv i η w + η w * spatialDeriv i d w) y =
      spatialDeriv j (fun w => d w * spatialDeriv i η w) y +
        spatialDeriv j (fun w => η w * spatialDeriv i d w) y := by
    change spatialDeriv j ((fun w => d w * spatialDeriv i η w) +
      (fun w => η w * spatialDeriv i d w)) y = _
    exact spatial_add_rule (hd.mul hηi) (hη.mul hdi) j y
  have hsecond' : spatialDeriv j
      (fun w => d w * spatialDeriv i η w) y =
      d y * spatialDeriv j (spatialDeriv i η) y +
        spatialDeriv i η y * spatialDeriv j d y := by
    convert hsecond using 1 <;> rfl
  have hthird' : spatialDeriv j
      (fun w => η w * spatialDeriv i d w) y =
      η y * spatialDeriv j (spatialDeriv i d) y +
        spatialDeriv i d y * spatialDeriv j η y := by
    convert hthird using 1 <;> rfl
  rw [hadd', hsecond', hthird']
  rw [hdj_fun, hdij', hdi']
  have hdval : d y = q y - q z := rfl
  rw [hdval]
  ring_nf

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
