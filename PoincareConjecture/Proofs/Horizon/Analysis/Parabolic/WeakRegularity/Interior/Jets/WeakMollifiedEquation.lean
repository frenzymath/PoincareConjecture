




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakDivergence
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakConvolution








open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

open Poincare.Analysis.Parabolic.WeakRegularity.Interior

theorem mollified_principal_equation_of_forcing
    {n : ℕ} {U V : Set (Spacetime n)} (hU : IsOpen U) (hV : IsOpen V)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u f : Spacetime n → ℝ} (hu : LocallyIntegrableOn u U volume)
    (_hf : LocallyIntegrableOn f U volume)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y)
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    {η : Spacetime n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ x ∈ V, tsupport (translatedKernel η x) ⊆ U)
    {z : Spacetime n} (hz : z ∈ V) :
    C.operator (lebesgueConvolution η u) z =
      -(∑ i : Fin n, ∑ j : Fin n, (C.principal i j z * lebesgueConvolution (spatialDeriv i η) (g j) z -
        lebesgueConvolution (spatialDeriv i η) (fun y => C.principal i j y * g j y) z +
        lebesgueConvolution η (fun y => spatialDeriv i (C.principal i j) y * g j y) z)) +
      (∑ i : Fin n, (C.drift i z * lebesgueConvolution η (g i) z -
        lebesgueConvolution η (fun y => C.drift i y * g i y) z)) +
      C.zeroth z * lebesgueConvolution η u z -
        lebesgueConvolution η (fun y => C.zeroth y * u y) z + lebesgueConvolution η f z := by
  have hsz := hs z hz
  have hds (v : Spacetime n) :
      tsupport (translatedKernel (fun y => fderiv ℝ η y v) z) ⊆ U := by
    apply Subset.trans _ hsz
    change tsupport ((fun y => fderiv ℝ η y v) ∘ Homeomorph.subLeft z) ⊆
      tsupport (η ∘ Homeomorph.subLeft z)
    rw [tsupport_comp_eq_preimage, tsupport_comp_eq_preimage]
    exact preimage_mono (tsupport_fderiv_apply_subset ℝ v)
  have dsm (v : Spacetime n) : ContDiff ℝ ∞ (fun y => fderiv ℝ η y v) :=
    (hη.fderiv_right (by simp)).clm_apply contDiff_const
  have intconv {f κ : Spacetime n → ℝ} (hf : LocallyIntegrableOn f U volume)
      (hk : ContDiff ℝ ∞ κ) (hkc : HasCompactSupport κ)
      (hks : tsupport (translatedKernel κ z) ⊆ U) :
      Integrable (fun y => κ (z-y) * f y) (volume.restrict U) := by
    have hc : HasCompactSupport (translatedKernel κ z) :=
      hkc.comp_homeomorph (Homeomorph.subLeft z)
    have hi : Integrable (fun y => translatedKernel κ z y * f y) := by
      apply (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_left _ _).trans (subset_tsupport _))).mp
      exact (hf.integrableOn_compact_subset hks hc).continuousOn_mul
        (hk.continuous.comp (continuous_const.sub continuous_id)).continuousOn hc
    exact hi.integrableOn
  have evalconv {f κ : Spacetime n → ℝ}
      (hks : tsupport (translatedKernel κ z) ⊆ U) :
      (∫ y in U, κ (z-y) * f y) = lebesgueConvolution κ f z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    exact mul_eq_zero_of_left
      (image_eq_zero_of_notMem_tsupport (f := translatedKernel κ z)
        (fun h => hy (hks h))) _
  have hci (i j) : LocallyIntegrableOn
      (fun y => C.principal i j y * g j y) U volume :=
    (hg j).continuousOn_mul (hC.1 i j).continuousOn hU.isLocallyClosed
  have hcd (i j) : LocallyIntegrableOn
      (fun y => spatialDeriv i (C.principal i j) y * g j y) U volume := by
    have hreg : ContDiffOn ℝ ∞ (spatialDeriv i (C.principal i j)) U :=
      ((hC.1 i j).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    exact (hg j).continuousOn_mul hreg.continuousOn hU.isLocallyClosed
  have hbi (i) : LocallyIntegrableOn (fun y => C.drift i y * g i y) U volume :=
    (hg i).continuousOn_mul (hC.2.1 i).continuousOn hU.isLocallyClosed
  have hzi : LocallyIntegrableOn (fun y => C.zeroth y * u y) U volume :=
    hu.continuousOn_mul hC.2.2.continuousOn hU.isLocallyClosed
  let T := translatedKernel η z
  have hT : ContDiff ℝ ∞ T := hη.comp (contDiff_const.sub contDiff_id)
  have hTc : HasCompactSupport T := hηc.comp_homeomorph (Homeomorph.subLeft z)
  have htder (y v : Spacetime n) : fderiv ℝ T y v = -fderiv ℝ η (z-y) v := by
    have hd := (hη.differentiable (by simp) (z-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
    change HasFDerivAt T _ y at hd
    rw [hd.fderiv]
    simp
  have hp (i j : Fin n) {y : Spacetime n} (hy : y ∈ U) :
      spatialDeriv i (fun x => C.principal i j x * T x) y =
        spatialDeriv i (C.principal i j) y * η (z-y) -
          C.principal i j y * spatialDeriv i η (z-y) := by
    have hc := ((hC.1 i j y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    dsimp only [spatialDeriv]
    rw [fderiv_fun_mul hc (hT.differentiable (by simp) y)]
    simp only [_root_.add_apply, _root_.smul_apply,
      smul_eq_mul, htder]
    dsimp only [T, translatedKernel]
    ring
  have he := (first_order_pairing_eq_adjoint hU hC hu hg hweak hT hTc hsz).trans
    (hforce T hT hTc hsz)
  change _ = lebesgueConvolution η f z at he
  have he' : (∫ y in U, timeDeriv η (z-y) * u y +
      (∑ i, ∑ j, (η (z-y) * (spatialDeriv i (C.principal i j) y * g j y) -
        spatialDeriv i η (z-y) * (C.principal i j y * g j y))) +
      (∑ i, η (z-y) * (C.drift i y * g i y)) +
      η (z-y) * (C.zeroth y * u y)) = lebesgueConvolution η f z := by
    rw [← he]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    have ht : timeDeriv T y = -timeDeriv η (z-y) := htder y (0, 1)
    apply congrArg₂ (· + ·)
    · apply congrArg₂ (· + ·)
      · apply congrArg₂ (· + ·)
        · rw [ht]
          ring
        · apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hp i j hy]
          ring
      · apply Finset.sum_congr rfl
        intro i _
        dsimp only [T, translatedKernel]
        ring
    · dsimp only [T, translatedKernel]
      ring
  have it : Integrable (fun y => timeDeriv η (z-y) * u y) (volume.restrict U) :=
    intconv hu (dsm (0, 1)) (hηc.fderiv_apply ℝ (0, 1)) (hds (0, 1))
  have ia (i j) := intconv (hcd i j) hη hηc hsz
  have ib (i j) : Integrable
      (fun y => spatialDeriv i η (z-y) * (C.principal i j y * g j y)) (volume.restrict U) :=
    intconv (hci i j) (dsm (spatialDirection i))
      (hηc.fderiv_apply ℝ _) (hds (spatialDirection i))
  have ic (i) := intconv (hbi i) hη hηc hsz
  have iz := intconv hzi hη hηc hsz
  have sumI {ι : Type} [Fintype ι] (f : ι → Spacetime n → ℝ)
      (hf : ∀ i, Integrable (f i) (volume.restrict U)) :
      Integrable (fun y => ∑ i, f i y) (volume.restrict U) :=
    integrable_finsetSum _ (fun i _ => hf i)
  have iab (i j) : Integrable (fun y =>
      η (z-y) * (spatialDeriv i (C.principal i j) y * g j y) -
        spatialDeriv i η (z-y) * (C.principal i j y * g j y)) (volume.restrict U) :=
    (ia i j).sub (ib i j)
  have iabs := sumI (ι := Fin n) _ (fun i => sumI (ι := Fin n) _ (iab i))
  have ics := sumI (ι := Fin n) _ ic
  have hlin : lebesgueConvolution (timeDeriv η) u z +
      (∑ i, ∑ j, (lebesgueConvolution η
        (fun y => spatialDeriv i (C.principal i j) y * g j y) z -
        lebesgueConvolution (spatialDeriv i η) (fun y => C.principal i j y * g j y) z)) +
      (∑ i, lebesgueConvolution η (fun y => C.drift i y * g i y) z) +
      lebesgueConvolution η (fun y => C.zeroth y * u y) z = lebesgueConvolution η f z := by
    have h1 := integral_add ((it.add iabs).add ics) iz
    have h2 := integral_add (it.add iabs) ics
    have h3 := integral_add it iabs
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3, integral_finsetSum _ (fun i _ => sumI _ (iab i)),
      integral_finsetSum _ (fun i _ => ic i)] at he'
    simp_rw [integral_finsetSum _ (fun j _ => iab _ j),
      integral_sub (ia _ _) (ib _ _)] at he'
    have et : (∫ y in U, timeDeriv η (z-y) * u y) =
        lebesgueConvolution (timeDeriv η) u z :=
      evalconv (κ := timeDeriv η) (hds (0, 1))
    have es (i : Fin n) (f : Spacetime n → ℝ) :
        (∫ y in U, spatialDeriv i η (z-y) * f y) =
          lebesgueConvolution (spatialDeriv i η) f z :=
      evalconv (κ := spatialDeriv i η) (hds (spatialDirection i))
    simpa only [evalconv hsz, et, es] using he'
  have hfirst (j : Fin n) {x : Spacetime n} (hx : x ∈ V) :
      spatialDeriv j (lebesgueConvolution η u) x = lebesgueConvolution η (g j) x :=
    fderiv_lebesgueConvolution_eq_weakDerivative hU hu (hg j) (hweak j) hη hηc (hs x hx)
  have hsecond (i j : Fin n) :
      spatialDeriv i (spatialDeriv j (lebesgueConvolution η u)) z =
        lebesgueConvolution (spatialDeriv i η) (g j) z := by
    have hh : spatialDeriv j (lebesgueConvolution η u) =ᶠ[𝓝 z]
        lebesgueConvolution η (g j) := by
      filter_upwards [hV.mem_nhds hz] with x hx
      exact hfirst j hx
    change fderiv ℝ _ z (spatialDirection i) = _
    rw [hh.fderiv_eq]
    exact fderiv_lebesgueConvolution_locallyIntegrableOn hU (hg j) hη hηc hsz
  have ht : timeDeriv (lebesgueConvolution η u) z = lebesgueConvolution (timeDeriv η) u z :=
    fderiv_lebesgueConvolution_locallyIntegrableOn hU hu hη hηc hsz
  simp only [Coefficients.operator, ht, hsecond, hfirst _ hz,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at hlin ⊢
  linarith

theorem WeakSolutionOn.mollified_principal_equation
    {n : ℕ} {U V : Set (Spacetime n)} (hU : IsOpen U) (hV : IsOpen V)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hw : WeakSolutionOn C u U)
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, LocallyIntegrableOn (g i) U volume)
    (hweak : ∀ i (ψ : Spacetime n → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * g i y) = -(∫ y in U, spatialDeriv i ψ y * u y))
    {η : Spacetime n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ x ∈ V, tsupport (translatedKernel η x) ⊆ U)
    {z : Spacetime n} (hz : z ∈ V) :
    C.operator (lebesgueConvolution η u) z =
      -(∑ i : Fin n, ∑ j : Fin n, (C.principal i j z * lebesgueConvolution (spatialDeriv i η) (g j) z -
        lebesgueConvolution (spatialDeriv i η) (fun y => C.principal i j y * g j y) z +
        lebesgueConvolution η (fun y => spatialDeriv i (C.principal i j) y * g j y) z)) +
      (∑ i : Fin n, (C.drift i z * lebesgueConvolution η (g i) z -
        lebesgueConvolution η (fun y => C.drift i y * g i y) z)) +
      C.zeroth z * lebesgueConvolution η u z -
        lebesgueConvolution η (fun y => C.zeroth y * u y) z := by
  have hforce (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
      (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * (0 : ℝ) := by
    simpa only [mul_zero, integral_zero] using hw.2 φ hφ hφc hφU
  have hh := mollified_principal_equation_of_forcing hU hV hC hw.1
    locallyIntegrableOn_zero hforce hg hweak hη hηc hs hz
  have hzero : lebesgueConvolution η (fun _ : Spacetime n => (0 : ℝ)) z = 0 := by
    simp only [lebesgueConvolution, mul_zero, integral_zero]
  simpa only [hzero, add_zero] using hh


end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
