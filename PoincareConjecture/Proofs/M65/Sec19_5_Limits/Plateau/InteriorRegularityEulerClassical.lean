import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerFields
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

private theorem compact_continuous_memLp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set LoopPlane} (hK : IsCompact K)
    {f : LoopPlane → E} (hf : ContinuousOn f K) : MemLp f 2 (volume.restrict K) := by
  have hm : AEStronglyMeasurable f (volume.restrict K) :=
    hf.aestronglyMeasurable hK.measurableSet
  exact (memLp_two_iff_integrable_sq_norm hm).mpr
    ((hf.norm.pow 2).integrableOn_compact hK)

theorem classical_scalar_weak_identity {U : Set LoopPlane} (hU : IsOpen U)
    {f : LoopPlane → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test) (hs : tsupport test ⊆ U)
    (v : LoopPlane) :
    IntegrableOn (fun z => fderiv ℝ f z v * test z) U ∧
      IntegrableOn (fun z => f z * fderiv ℝ test z v) U ∧
      (∫ z in U, fderiv ℝ f z v * test z) =
        -(∫ z in U, f z * fderiv ℝ test z v) := by
  have hD : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have htestD : Continuous (fun z => fderiv ℝ test z v) :=
    ((test.smooth 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupD : tsupport (fun z => fderiv ℝ test z v) ⊆ tsupport test :=
    tsupport_fderiv_apply_subset ℝ v
  have hI1 : Integrable (fun z => fderiv ℝ f z v * test z) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport test))).mp
    exact ((hD.mono hs).mul test.continuous.continuousOn).integrableOn_compact hc
  have hI2 : Integrable (fun z => f z * fderiv ℝ test z v) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans hsupD))).mp
    exact ((hf.continuousOn.mono hs).mul htestD.continuousOn).integrableOn_compact hc
  have hI0 : Integrable (fun z => f z * test z) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport test))).mp
    exact ((hf.continuousOn.mono hs).mul test.continuous.continuousOn).integrableOn_compact hc
  have hw := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI1 hI2 hI0
    (fun z hz => ((hf z (hs hz)).contDiffAt (hU.mem_nhds (hs hz))).differentiableAt one_ne_zero)
    (fun z _ => test.differentiableAt (x := z))
  refine ⟨hI1.integrableOn, hI2.integrableOn, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hs hm)), mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [fderiv_of_notMem_tsupport ℝ (fun hm => hz (hs hm)), zero_apply, mul_zero])]
  linarith only [hw]

def classicalMap {M : Type u} {N : ℕ} (e : M → EuclideanSpace ℝ (Fin N))
    {U : Set LoopPlane} (hU : IsOpen U) (q : LoopPlane → M)
    (hq : ContDiffOn ℝ 1 (e ∘ q) U) : M65LocalWeakMap e U where
  value := q
  derivative i z := fderiv ℝ (e ∘ q) z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  value_memLp K hK hKU := compact_continuous_memLp hK (hq.continuousOn.mono hKU)
  derivative_memLp i K hK hKU := compact_continuous_memLp hK
    (((hq.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hKU)
  weak_derivative test hc hs i j := by
    let b := EuclideanSpace.basisFun (Fin 2) ℝ i
    let f := fun z => e (q z) j
    have hf : ContDiffOn ℝ 1 f U :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hq
    have hd (z : LoopPlane) (hz : z ∈ U) :
        fderiv ℝ f z b = (fderiv ℝ (e ∘ q) z b) j := by
      have hh := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z
        (((hq z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero).hasFDerivAt
      exact congrArg (fun L => L b) hh.fderiv
    have hw := (classical_scalar_weak_identity hU hf test hc hs b).2.2
    calc
      _ = ∫ z in U, fderiv ℝ f z b * test z := by
        apply setIntegral_congr_fun hU.measurableSet
        intro z hz
        change test z * (fderiv ℝ (e ∘ q) z b) j = fderiv ℝ f z b * test z
        rw [hd z hz, mul_comm]
      _ = -(∫ z in U, f z * fderiv ℝ test z b) := hw
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun z => mul_comm _ _

theorem classical_derivative_eq_weak {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (hU : IsOpen U) (F : M65LocalWeakMap e U) (q : LoopPlane → M)
    (hq : ContDiffOn ℝ 1 (e ∘ q) U)
    (hvalue : (fun z => e (q z)) =ᵐ[volume.restrict U] fun z => e (F.value z))
    (i : Fin 2) :
    (fun z => fderiv ℝ (e ∘ q) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      =ᵐ[volume.restrict U] F.derivative i :=
  derivative_unique hU (classicalMap e hU q hq) F hvalue i

end PoincareConjecture.M65Euler
