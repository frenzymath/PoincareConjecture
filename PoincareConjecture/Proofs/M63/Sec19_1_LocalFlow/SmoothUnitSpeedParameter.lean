import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UnitSpeedInitialPeriod
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem speed_contDiff_of_smooth (F : RicciFlow n M (Icc a b))
    (q : ℝ → ℝ → M) {t : ℝ}
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => q x t))
    (himm : ∀ x, curveVelocity (n := n) (fun y => q y t) x ≠ 0) :
    ContDiff ℝ ∞ (curveSpeed F q t) := by
  have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun x : ℝ => (⟨x, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  have hX : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x => (⟨q x t, curveVelocity (n := n) (fun y => q y t) x⟩ :
        TangentBundle (𝓡 n) M)) :=
    (hspace.contMDiff_tangentMap (m := ∞) (by simp)).comp hone
  have hpair : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun x => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (q x t)
        ((F.metric t).inner (q x t) (curveVelocity (fun y => q y t) x)
          (curveVelocity (fun y => q y t) x))) :=
    ((F.metric t).contMDiff.comp hspace).clm_bundle_apply₂ hX hX
  have hsq : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x => (F.metric t).inner (q x t) (curveVelocity (fun y => q y t) x)
        (curveVelocity (fun y => q y t) x)) := by
    intro x
    exact (Bundle.contMDiffAt_totalSpace.mp (hpair x)).2
  exact hsq.contDiff.sqrt fun x => ((F.metric t).pos _ _ (himm x)).ne'

theorem exists_smooth_unit_speed_parameter (F : RicciFlow n M (Icc a b))
    (gamma : ℝ → M) (t : ℝ) (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    let v := curveSpeed F (fun x _ => gamma x) t
    let ell := ∫ x in (0 : ℝ)..curvePeriod, v x
    0 < ell ∧ ∃ sigma : ℝ ≃ₜ ℝ,
      (∀ x, sigma x = ∫ y in (0 : ℝ)..x, v y) ∧
      ContDiff ℝ ∞ (sigma : ℝ → ℝ) ∧ ContDiff ℝ ∞ (sigma.symm : ℝ → ℝ) ∧
      sigma 0 = 0 ∧ (∀ x, 0 < deriv sigma x) ∧ (∀ y, 0 < deriv sigma.symm y) ∧
      (∀ x, sigma (x + curvePeriod) = sigma x + ell) ∧
      (∀ y, sigma.symm (y + ell) = sigma.symm y + curvePeriod) ∧
      Function.Periodic (fun y => gamma (sigma.symm y)) ell ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => gamma (sigma.symm y)) ∧
      (∀ y, curveVelocity (n := n) (fun z => gamma (sigma.symm z)) y ≠ 0) ∧
      (∀ y, curveSpeed F (fun z _ => gamma (sigma.symm z)) t y = 1) ∧
      (∀ y, (curveSpeed F (fun z _ => gamma (sigma.symm z)) t y ^ 2)⁻¹ = 1) ∧
      ∀ x, gamma (sigma.symm (sigma x)) = gamma x := by
  let v := curveSpeed F (fun x _ => gamma x) t
  obtain ⟨hell, sigma, hformula, hsigma, _hinv, hzero, hpos, hinvpos, hshift,
      hinvshift, hper, _hreg, himm', hunit, hprincipal, hrecovery⟩ :=
    exists_c2_unit_speed_parameter F gamma t hperiod
      (hgamma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) himm
  have hv : ContDiff ℝ ∞ v :=
    speed_contDiff_of_smooth F (fun x _ => gamma x) hgamma himm
  have hd (x : ℝ) : HasDerivAt sigma (v x) x := by
    have hprimitive : (sigma : ℝ → ℝ) = fun x => ∫ y in (0 : ℝ)..x, v y :=
      funext hformula
    rw [hprimitive]
    exact intervalIntegral.integral_hasDerivAt_right
      (hv.continuous.intervalIntegrable 0 x) (hv.continuous.stronglyMeasurableAtFilter _ _)
      hv.continuous.continuousAt
  have hderiv : deriv sigma = v := funext fun x => (hd x).deriv
  have hsmooth : ContDiff ℝ ∞ (sigma : ℝ → ℝ) :=
    contDiff_infty_iff_deriv.mpr
      ⟨hsigma.differentiable (by norm_num), hderiv ▸ hv⟩
  have hinvsmooth : ContDiff ℝ ∞ (sigma.symm : ℝ → ℝ) :=
    sigma.contDiff_symm_deriv (fun x => by simpa only [← hderiv] using (hpos x).ne')
      hd hsmooth
  exact ⟨hell, sigma, hformula, hsmooth, hinvsmooth, hzero, hpos, hinvpos, hshift,
    hinvshift, hper, hgamma.comp hinvsmooth.contMDiff, himm', hunit, hprincipal, hrecovery⟩

end PoincareConjecture.M63
