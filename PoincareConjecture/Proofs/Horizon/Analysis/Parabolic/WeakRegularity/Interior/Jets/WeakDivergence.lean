import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.AdjointIdentity

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

theorem first_order_pairing_eq_adjoint
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : LocallyIntegrableOn u U volume)
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y in U, -u y * timeDeriv φ y +
      (∑ i, ∑ j, g j y * spatialDeriv i (fun x => C.principal i j x * φ x) y) +
      (∑ i, g i y * (C.drift i y * φ y)) + u y * (C.zeroth y * φ y)) =
      ∫ y, u y * C.adjoint φ y := by
  have smooth {f : Spacetime n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
      (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport f
    · exact (hf y (hs hy)).contDiffAt (hU.mem_nhds (hs hy))
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hy)
  have deriv_smooth {f : Spacetime n → ℝ} (hf : ContDiff ℝ ∞ f)
      (v : Spacetime n) : ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have integ {v ψ : Spacetime n → ℝ} (hv : LocallyIntegrableOn v U volume)
      (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
      Integrable (fun y => v y * ψ y) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right v ψ).trans (subset_tsupport ψ))).mp
    exact (hv.integrableOn_compact_subset hψU hψc).mul_continuousOn
      hψ.continuous.continuousOn hψc
  have restrict {v ψ : Spacetime n → ℝ} (hψU : tsupport ψ ⊆ U) :
      (∫ y in U, v y * ψ y) = ∫ y, v y * ψ y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψU h)), mul_zero]
  have weak (i : Fin n) {ψ : Spacetime n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
      (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
      (∫ y, g i y * ψ y) = -(∫ y, u y * spatialDeriv i ψ y) := by
    have hh := hweak i ψ hψ hψc hψU
    simp only [mul_comm] at hh
    rw [restrict hψU, restrict (ψ := spatialDeriv i ψ)
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans hψU)] at hh
    exact hh
  let A := fun i j y => C.principal i j y * φ y
  let B := fun i y => C.drift i y * φ y
  let Z := fun y => C.zeroth y * φ y
  have hAU (i j) : tsupport (A i j) ⊆ U := tsupport_mul_subset_right.trans hφU
  have hBU (i) : tsupport (B i) ⊆ U := tsupport_mul_subset_right.trans hφU
  have hZU : tsupport Z ⊆ U := tsupport_mul_subset_right.trans hφU
  have hA (i j) : ContDiff ℝ ∞ (A i j) :=
    smooth ((hC.1 i j).mul hφ.contDiffOn) (hAU i j)
  have hB (i) : ContDiff ℝ ∞ (B i) :=
    smooth ((hC.2.1 i).mul hφ.contDiffOn) (hBU i)
  have hZ : ContDiff ℝ ∞ Z := smooth (hC.2.2.mul hφ.contDiffOn) hZU
  have hAc (i j) : HasCompactSupport (A i j) := hφc.mul_left
  have hBc (i) : HasCompactSupport (B i) := hφc.mul_left
  have hZc : HasCompactSupport Z := hφc.mul_left
  have hAD (i j) : ContDiff ℝ ∞ (spatialDeriv i (A i j)) :=
    deriv_smooth (hA i j) _
  have hADc (i j) : HasCompactSupport (spatialDeriv i (A i j)) :=
    (hAc i j).fderiv_apply ℝ _
  have hADU (i j) : tsupport (spatialDeriv i (A i j)) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ _).trans (hAU i j)
  have hT : Integrable (fun y => u y * timeDeriv φ y) :=
    integ hu (deriv_smooth hφ (0, 1)) (hφc.fderiv_apply ℝ (0, 1))
    ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hφU)
  have hLa (i j) : Integrable (fun y =>
      u y * spatialDeriv j (spatialDeriv i (A i j)) y) :=
    integ hu (deriv_smooth (hAD i j) (spatialDirection j))
    ((hADc i j).fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans (hADU i j))
  have hLb (i) : Integrable (fun y => u y * spatialDeriv i (B i) y) :=
    integ hu (deriv_smooth (hB i) (spatialDirection i))
    ((hBc i).fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans (hBU i))
  have hRa (i j) := integ (hg j) (hAD i j) (hADc i j) (hADU i j)
  have hRb (i) := integ (hg i) (hB i) (hBc i) (hBU i)
  have hzero := integ hu hZ hZc hZU
  have sumI {ι : Type} [Fintype ι] (f : ι → Spacetime n → ℝ)
      (hf : ∀ i, Integrable (f i)) : Integrable (fun y => ∑ i, f i y) :=
    integrable_finsetSum _ (fun i _ => hf i)
  have hLas := sumI (ι := Fin n) _ (fun i => sumI (ι := Fin n) _ (hLa i))
  have hLbs := sumI (ι := Fin n) _ hLb
  have hRas := sumI (ι := Fin n) _ (fun i => sumI (ι := Fin n) _ (hRa i))
  have hRbs := sumI (ι := Fin n) _ hRb
  have ha (i j) := weak j (hAD i j) (hADc i j) (hADU i j)
  have hb (i) := weak i (hB i) (hBc i) (hBU i)
  have heq : (∫ y, -u y * timeDeriv φ y +
      (∑ i, ∑ j, g j y * spatialDeriv i (A i j) y) +
      (∑ i, g i y * B i y) + u y * Z y) = ∫ y, u y * C.adjoint φ y := by
    calc
      _ = -(∫ y, u y * timeDeriv φ y) +
          (∑ i, ∑ j, ∫ y, g j y * spatialDeriv i (A i j) y) +
          (∑ i, ∫ y, g i y * B i y) + ∫ y, u y * Z y := by
        simp only [neg_mul]
        have h1 := integral_add ((hT.neg.add hRas).add hRbs) hzero
        have h2 := integral_add (hT.neg.add hRas) hRbs
        have h3 := integral_add hT.neg hRas
        simp only [Pi.add_apply, Pi.neg_apply] at h1 h2 h3
        rw [h1, h2, h3, integral_neg,
          integral_finsetSum _ (fun i _ => sumI _ (hRa i)),
          integral_finsetSum _ (fun i _ => hRb i)]
        simp_rw [integral_finsetSum _ (fun j _ => hRa _ j)]
      _ = -(∫ y, u y * timeDeriv φ y) -
          (∑ i, ∑ j, ∫ y, u y * spatialDeriv j (spatialDeriv i (A i j)) y) -
          (∑ i, ∫ y, u y * spatialDeriv i (B i) y) + ∫ y, u y * Z y := by
        simp only [ha, hb, Finset.sum_neg_distrib, sub_eq_add_neg]
      _ = ∫ y, -(u y * timeDeriv φ y) -
          (∑ i, ∑ j, u y * spatialDeriv j (spatialDeriv i (A i j)) y) -
          (∑ i, u y * spatialDeriv i (B i) y) + u y * Z y := by
        have h1 := integral_add ((hT.neg.sub hLas).sub hLbs) hzero
        have h2 := integral_sub (hT.neg.sub hLas) hLbs
        have h3 := integral_sub hT.neg hLas
        simp only [Pi.sub_apply, Pi.neg_apply] at h1 h2 h3
        rw [h1, h2, h3, integral_neg,
          integral_finsetSum _ (fun i _ => sumI _ (hLa i)),
          integral_finsetSum _ (fun i _ => hLb i)]
        simp_rw [integral_finsetSum _ (fun j _ => hLa _ j)]
      _ = _ := by
        congr 1
        funext y
        simp only [Coefficients.adjoint, A, B, Z, mul_add, mul_sub, mul_neg,
          Finset.mul_sum]
  have hrestrict : (∫ y in U, -u y * timeDeriv φ y +
      (∑ i, ∑ j, g j y * spatialDeriv i (A i j) y) +
      (∑ i, g i y * B i y) + u y * Z y) = ∫ y, -u y * timeDeriv φ y +
      (∑ i, ∑ j, g j y * spatialDeriv i (A i j) y) +
      (∑ i, g i y * B i y) + u y * Z y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz {ψ : Spacetime n → ℝ} (hψU : tsupport ψ ⊆ U) : ψ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hψU h))
    have ht : timeDeriv φ y = 0 :=
      hz ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hφU)
    simp only [ht, hz (hADU _ _), hz (hBU _), hz hZU, mul_zero,
      Finset.sum_const_zero, add_zero]
  exact hrestrict.trans heq

theorem WeakSolutionOn.first_order_pairing
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hw : WeakSolutionOn C u U)
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ y in U, -u y * timeDeriv φ y +
      (∑ i, ∑ j, g j y * spatialDeriv i (fun x => C.principal i j x * φ x) y) +
      (∑ i, g i y * (C.drift i y * φ y)) + u y * (C.zeroth y * φ y)) = 0 := by
  exact (first_order_pairing_eq_adjoint hU hC hw.1 hg hweak hφ hφc hφU).trans
    (hw.2 φ hφ hφc hφU)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
