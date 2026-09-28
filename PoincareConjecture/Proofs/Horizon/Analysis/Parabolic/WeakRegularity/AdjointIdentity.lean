




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos










open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem smooth_directional (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (v : Spacetime n) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem smooth_of_support (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact (hf z (hs hz)).contDiffAt (hU.mem_nhds (hs hz))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

private theorem integrable_mul_test {f g : Spacetime n → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f g).trans (subset_tsupport g))).mp
  exact ((hf.mul hg).mono hgU).integrableOn_compact hgc

private theorem integral_directional_test (hU : IsOpen U)
    {f g : Spacetime n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U)
    (v : Spacetime n) :
    (∫ z, f z * fderiv ℝ g z v) = -∫ z, fderiv ℝ f z v * g z := by
  have hgd := smooth_directional hU hg.contDiffOn v
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_test (smooth_directional hU hf v).continuousOn
      hg.continuous.continuousOn hgc hgU
  · exact integrable_mul_test hf.continuousOn hgd.continuousOn
      (hgc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hgU)
  · exact integrable_mul_test hf.continuousOn hg.continuous.continuousOn hgc hgU
  · intro z hz
    exact ((hf z (hgU hz)).contDiffAt (hU.mem_nhds (hgU hz))).differentiableAt
      (by simp)
  · intro z _
    exact hg.differentiable (by simp) z

private theorem integral_second_test (hU : IsOpen U)
    {f g : Spacetime n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U)
    (v w : Spacetime n) :
    (∫ z, f z * fderiv ℝ (fun y => fderiv ℝ g y v) z w) =
      ∫ z, fderiv ℝ (fun y => fderiv ℝ f y w) z v * g z := by
  have hgd : ContDiff ℝ ∞ (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (by simp)).clm_apply contDiff_const
  rw [integral_directional_test hU hf hgd (hgc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hgU) w]
  rw [integral_directional_test hU (smooth_directional hU hf w) hg hgc hgU v]
  simp

theorem integral_adjoint_eq {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    (C : Coefficients n) (hC : C.IsSmoothOn U)
    {u φ : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, u z * C.adjoint φ z) = ∫ z, φ z * C.operator u z := by
  let A := fun i j z => C.principal i j z * φ z
  let B := fun i z => C.drift i z * φ z
  have hAU (i j) : tsupport (A i j) ⊆ U := tsupport_mul_subset_right.trans hφU
  have hBU (i) : tsupport (B i) ⊆ U := tsupport_mul_subset_right.trans hφU
  have hA (i j) : ContDiff ℝ ∞ (A i j) :=
    smooth_of_support hU ((hC.1 i j).mul hφ.contDiffOn) (hAU i j)
  have hB (i) : ContDiff ℝ ∞ (B i) :=
    smooth_of_support hU ((hC.2.1 i).mul hφ.contDiffOn) (hBU i)
  have hAc (i j) : HasCompactSupport (A i j) := hφc.mul_left
  have hBc (i) : HasCompactSupport (B i) := hφc.mul_left
  have hsd {f : Spacetime n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (i : Fin n) :
      ContDiffOn ℝ ∞ (spatialDeriv i f) U := smooth_directional hU hf _
  have htd {f : Spacetime n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ContDiffOn ℝ ∞ (timeDeriv f) U := smooth_directional hU hf _
  have hLt : Integrable (fun z => u z * timeDeriv φ z) :=
    integrable_mul_test hu.continuousOn (htd hφ.contDiffOn).continuousOn
      (hφc.fderiv_apply ℝ (0, 1)) ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hφU)
  have hLa (i j) : Integrable (fun z =>
      u z * spatialDeriv j (spatialDeriv i (A i j)) z) :=
    integrable_mul_test hu.continuousOn
      (hsd (hsd (hA i j).contDiffOn i) j).continuousOn
      (((hAc i j).fderiv_apply ℝ (spatialDirection i)).fderiv_apply ℝ (spatialDirection j))
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection j)).trans
        ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans (hAU i j)))
  have hLb (i) : Integrable (fun z => u z * spatialDeriv i (B i) z) :=
    integrable_mul_test hu.continuousOn (hsd (hB i).contDiffOn i).continuousOn
      ((hBc i).fderiv_apply ℝ (spatialDirection i))
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans (hBU i))
  have hRt : Integrable (fun z => timeDeriv u z * φ z) :=
    integrable_mul_test (htd hu).continuousOn hφ.continuous.continuousOn hφc hφU
  have hRa (i j) : Integrable (fun z =>
      spatialDeriv i (spatialDeriv j u) z * A i j z) :=
    integrable_mul_test (hsd (hsd hu j) i).continuousOn
      (hA i j).continuous.continuousOn (hAc i j) (hAU i j)
  have hRb (i) : Integrable (fun z => spatialDeriv i u z * B i z) :=
    integrable_mul_test (hsd hu i).continuousOn (hB i).continuous.continuousOn
      (hBc i) (hBU i)
  have hc : Integrable (fun z => (C.zeroth z * u z) * φ z) :=
    integrable_mul_test (hC.2.2.mul hu).continuousOn hφ.continuous.continuousOn hφc hφU
  have sumI {ι : Type} [Fintype ι] (f : ι → Spacetime n → ℝ)
      (hf : ∀ i, Integrable (f i)) : Integrable (fun z => ∑ i, f i z) :=
    integrable_finsetSum _ (fun i _ => hf i)
  have hLas := sumI (ι := Fin n) _ (fun i => sumI (ι := Fin n) _ (hLa i))
  have hLbs := sumI (ι := Fin n) _ hLb
  have hRas := sumI (ι := Fin n) _ (fun i => sumI (ι := Fin n) _ (hRa i))
  have hRbs := sumI (ι := Fin n) _ hRb
  have ht : (∫ z, u z * timeDeriv φ z) = -∫ z, timeDeriv u z * φ z :=
    integral_directional_test hU hu hφ hφc hφU (0, 1)
  have ha (i j) : (∫ z, u z * spatialDeriv j (spatialDeriv i (A i j)) z) =
      ∫ z, spatialDeriv i (spatialDeriv j u) z * A i j z :=
    integral_second_test hU hu (hA i j) (hAc i j) (hAU i j)
      (spatialDirection i) (spatialDirection j)
  have hb (i) : (∫ z, u z * spatialDeriv i (B i) z) =
      -∫ z, spatialDeriv i u z * B i z :=
    integral_directional_test hU hu (hB i) (hBc i) (hBU i) (spatialDirection i)
  change (∫ z, u z * C.adjoint φ z) = ∫ z, φ z * C.operator u z
  calc
    (∫ z, u z * C.adjoint φ z) =
        ∫ z, -(u z * timeDeriv φ z) -
          (∑ i, ∑ j, u z * spatialDeriv j (spatialDeriv i (A i j)) z) -
          (∑ i, u z * spatialDeriv i (B i) z) + (C.zeroth z * u z) * φ z := by
      congr 1
      funext z
      simp only [Coefficients.adjoint, A, B, mul_add, mul_sub, mul_neg, Finset.mul_sum]
      ring
    _ = -(∫ z, u z * timeDeriv φ z) -
          (∑ i, ∑ j, ∫ z, u z * spatialDeriv j (spatialDeriv i (A i j)) z) -
          (∑ i, ∫ z, u z * spatialDeriv i (B i) z) + ∫ z, (C.zeroth z * u z) * φ z := by
      have h1 := integral_add ((hLt.neg.sub hLas).sub hLbs) hc
      have h2 := integral_sub (hLt.neg.sub hLas) hLbs
      have h3 := integral_sub hLt.neg hLas
      simp only [Pi.sub_apply, Pi.neg_apply] at h1 h2 h3
      rw [h1, h2, h3, integral_neg]
      rw [integral_finsetSum _ (fun i _ => sumI _ (hLa i)),
        integral_finsetSum _ (fun i _ => hLb i)]
      simp_rw [integral_finsetSum _ (fun j _ => hLa _ j)]
    _ = (∫ z, timeDeriv u z * φ z) -
          (∑ i, ∑ j, ∫ z, spatialDeriv i (spatialDeriv j u) z * A i j z) +
          (∑ i, ∫ z, spatialDeriv i u z * B i z) + ∫ z, (C.zeroth z * u z) * φ z := by
      simp only [ht, ha, hb, Finset.sum_neg_distrib]
      ring
    _ = ∫ z, timeDeriv u z * φ z -
          (∑ i, ∑ j, spatialDeriv i (spatialDeriv j u) z * A i j z) +
          (∑ i, spatialDeriv i u z * B i z) + (C.zeroth z * u z) * φ z := by
      have h1 := integral_add ((hRt.sub hRas).add hRbs) hc
      have h2 := integral_add (hRt.sub hRas) hRbs
      have h3 := integral_sub hRt hRas
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
      rw [h1, h2, h3]
      rw [integral_finsetSum _ (fun i _ => sumI _ (hRa i)),
        integral_finsetSum _ (fun i _ => hRb i)]
      simp_rw [integral_finsetSum _ (fun j _ => hRa _ j)]
    _ = ∫ z, φ z * C.operator u z := by
      congr 1
      funext z
      simp only [Coefficients.operator, A, B, mul_add, mul_sub, Finset.mul_sum]
      simp only [mul_comm, mul_left_comm]

theorem weakSolutionOn_iff_operator_eq_zero {n : ℕ} {U : Set (Spacetime n)}
    (hU : IsOpen U) (C : Coefficients n) (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    WeakSolutionOn C u U ↔ ∀ z ∈ U, C.operator u z = 0 := by
  have hsd {f : Spacetime n → ℝ} (hf : ContDiffOn ℝ ∞ f U) (i : Fin n) :
      ContDiffOn ℝ ∞ (spatialDeriv i f) U := smooth_directional hU hf _
  have ht : ContDiffOn ℝ ∞ (timeDeriv u) U := smooth_directional hU hu _
  have ha : ContDiffOn ℝ ∞
      (fun z => ∑ i, ∑ j, C.principal i j z * spatialDeriv i (spatialDeriv j u) z) U := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hC.1 i j).mul (hsd (hsd hu j) i)
  have hb : ContDiffOn ℝ ∞ (fun z => ∑ i, C.drift i z * spatialDeriv i u z) U := by
    apply ContDiffOn.sum
    intro i _
    exact (hC.2.1 i).mul (hsd hu i)
  have hp : ContinuousOn (C.operator u) U :=
    (((ht.sub ha).add hb).add (hC.2.2.mul hu)).continuousOn
  constructor
  · intro hw
    have hae : ∀ᵐ z ∂volume, z ∈ U → C.operator u z = 0 := by
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hp.locallyIntegrableOn hU.measurableSet)
      intro φ hφ hφc hφU
      simpa only [smul_eq_mul] using
        (integral_adjoint_eq hU C hC hu hφ hφc hφU).symm.trans
          (hw.2 φ hφ hφc hφU)
    exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae)
      hU hp continuousOn_const
  · intro hz
    refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
    intro φ hφ hφc hφU
    rw [integral_adjoint_eq hU C hC hu hφ hφc hφU]
    apply integral_eq_zero_of_ae
    filter_upwards [] with z
    by_cases hzu : z ∈ U
    · simp only [hz z hzu, mul_zero, Pi.zero_apply]
    · simp only [image_eq_zero_of_notMem_tsupport (fun hs => hzu (hφU hs)),
        zero_mul, Pi.zero_apply]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
