import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialVariation
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ModelInverse
import PoincareConjecture.Proofs.M44.Mathlib.NearIdentity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

private theorem radialPhase_endpoint_derivative {f : E → E} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (v : E) :
    (fderiv ℝ (fun q => (f q, fderiv ℝ f q q)) p v).1 = fderiv ℝ f p v := by
  have hv : DifferentiableAt ℝ (fun q => fderiv ℝ f q q) p :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_id).differentiableAt (by simp)
  rw [((hf.differentiableAt (by simp)).hasFDerivAt.prodMk hv.hasFDerivAt).fderiv]
  rfl

namespace NormalizedCapExponential

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
  {Q : SurgeryCapClose g₀ S g tip scale eta}



theorem firstVariation_endpoint_derivative (D : NormalizedCapExponential Q R)
    {p : E} (hp : p ∈ ball 0 R) (v : E) :
    (firstVariation D.phase (p, v) 1).2.1 = fderiv ℝ D.coordinateMap p v := by
  simp only [firstVariation, phase, one_smul]
  exact radialPhase_endpoint_derivative
    (D.coordinateMap_smooth.contDiffAt (isOpen_ball.mem_nhds hp)) v

end NormalizedCapExponential



theorem standardFramePhase_firstVariation_endpoint_derivative
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (p v : E) :
    (firstVariation (standardFramePhase g₀ L) (p, v) 1).2.1 =
      fderiv ℝ (standardFrameExponential g₀ L) p v := by
  simp only [firstVariation, standardFramePhase, one_smul]
  exact radialPhase_endpoint_derivative (standardFrameExponential_contDiff g₀ L).contDiffAt v

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)





theorem tendstoUniformlyOn_initial_exponentials_C1
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {K : Set E} (hK : IsCompact K)
    (hKR : K ⊆ ball 0 (R / 2)) :
    TendstoUniformlyOn (fun n => (D n).coordinateMap) (standardFrameExponential g₀ L) atTop K ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (D n).coordinateMap)
        (fderiv ℝ (standardFrameExponential g₀ L)) atTop K := by
  have hvar := tendstoUniformlyOn_exponential_firstVariations g₀ S g tip scale eta Q D
    heta L hL hK (isCompact_closedBall (0 : E) 1) hKR
  have hread0 : UniformContinuous (fun z : (E × E) × (E × E) => z.1.1) :=
    uniformContinuous_fst.comp uniformContinuous_fst
  have hread1 : UniformContinuous (fun z : (E × E) × (E × E) => z.2.1) :=
    uniformContinuous_fst.comp uniformContinuous_snd
  have hvalue := ((hread0.comp_tendstoUniformlyOn hvar).comp
    (fun p : E => ((p, (0 : E)), (1 : ℝ)))).mono
      (fun _ hp => ⟨⟨hp, by simp⟩, by simp⟩ : K ⊆
        (fun p : E => ((p, (0 : E)), (1 : ℝ))) ⁻¹'
          ((K ×ˢ closedBall 0 1) ×ˢ Icc (0 : ℝ) 1))
  have hdir := ((hread1.comp_tendstoUniformlyOn hvar).comp
    (fun z : E × E => (z, (1 : ℝ)))).mono
      (fun _ hz => ⟨hz, by simp⟩ : K ×ˢ closedBall (0 : E) 1 ⊆
        (fun z : E × E => (z, (1 : ℝ))) ⁻¹'
          ((K ×ˢ closedBall 0 1) ×ˢ Icc (0 : ℝ) 1))
  constructor
  · simpa only [Function.comp_def, firstVariation, NormalizedCapExponential.phase,
      standardFramePhase, one_smul] using hvalue
  · apply TendstoUniformlyOn.clm_of_apply_unitBall
    rw [Metric.tendstoUniformlyOn_iff] at hdir ⊢
    intro epsilon hepsilon
    filter_upwards [hdir epsilon hepsilon] with n hn
    intro z hz
    have hp : z.1 ∈ ball (0 : E) R :=
      (ball_subset_ball (by linarith [(D 0).radius_pos])) (hKR hz.1)
    simpa only [Function.comp_apply, (D n).firstVariation_endpoint_derivative hp z.2,
      standardFramePhase_firstVariation_endpoint_derivative g₀ L z.1 z.2] using hn z hz




theorem tendstoUniformlyOn_fderiv_adjusted_exponentials
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {K : Set E} (hK : IsCompact K)
    (hKR : K ⊆ ball 0 (R / 2)) :
    TendstoUniformlyOn
      (fun n => fderiv ℝ (standardFrameLogarithm g₀ L ∘ (D n).coordinateMap))
      (fun _ => ContinuousLinearMap.id ℝ E) atTop K := by
  obtain ⟨hzero, hone⟩ :=
    tendstoUniformlyOn_initial_exponentials_C1 g₀ S g tip scale eta Q D heta L hL hK hKR
  have hder := tendstoUniformlyOn_fderiv_comp_of_compact hK isOpen_univ
    (fun x _ => ((standardFrameExponential_contDiff g₀ L).of_le (by simp)).contDiffAt (x := x))
    ((standardFrameLogarithm_contDiff g₀ L).of_le (by simp)).contDiffOn
    (fun _ _ => mem_univ _)
    (Eventually.of_forall fun n x hx =>
      ((D n).coordinateMap_smooth.contDiffAt (isOpen_ball.mem_nhds
        ((ball_subset_ball (by linarith [(D 0).radius_pos])) (hKR hx)))).differentiableAt (by simp))
    hzero hone
  have heq : standardFrameLogarithm g₀ L ∘ standardFrameExponential g₀ L = id :=
    funext (standardFrameLogarithm_exponential g₀ L)
  have hid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun _ => fderiv_id
  simpa only [heq, hid] using hder




theorem eventually_injOn_initial_exponentials
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKR : K ⊆ ball 0 (R / 2)) :
    ∀ᶠ n in atTop, InjOn (D n).map K := by
  have hder := tendstoUniformlyOn_fderiv_adjusted_exponentials
    g₀ S g tip scale eta Q D heta L hL hK hKR
  have hinj := TendstoUniformlyOn.eventually_injOn_of_fderiv_tendsto_id hconv
    (fun n x hx =>
      ((standardFrameLogarithm_contDiff g₀ L).differentiable (by simp) _).comp x
        (((D n).coordinateMap_smooth.contDiffAt (isOpen_ball.mem_nhds
          ((ball_subset_ball (by linarith [(D 0).radius_pos])) (hKR hx)))).differentiableAt
            (by simp))) hder
  filter_upwards [hinj] with n hn
  intro x hx y hy hxy
  apply hn hx hy
  exact congrArg (fun z => standardFrameLogarithm g₀ L ((Q n).inverse z)) hxy

end PoincareConjecture.M44
