import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialArclengthGauge
import Mathlib.Topology.Algebra.GroupWithZero

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_c2_unit_speed_parameter (F : RicciFlow n M (Icc a b))
    (gamma : ℝ → M) (t : ℝ) (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    let v := curveSpeed F (fun x _ => gamma x) t
    let ell := ∫ x in (0 : ℝ)..curvePeriod, v x
    0 < ell ∧ ∃ sigma : ℝ ≃ₜ ℝ,
      (∀ x, sigma x = ∫ y in (0 : ℝ)..x, v y) ∧
      ContDiff ℝ 2 (sigma : ℝ → ℝ) ∧ ContDiff ℝ 2 (sigma.symm : ℝ → ℝ) ∧
      sigma 0 = 0 ∧ (∀ x, 0 < deriv sigma x) ∧ (∀ y, 0 < deriv sigma.symm y) ∧
      (∀ x, sigma (x + curvePeriod) = sigma x + ell) ∧
      (∀ y, sigma.symm (y + ell) = sigma.symm y + curvePeriod) ∧
      Function.Periodic (fun y => gamma (sigma.symm y)) ell ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => gamma (sigma.symm y)) ∧
      (∀ y, curveVelocity (n := n) (fun z => gamma (sigma.symm z)) y ≠ 0) ∧
      (∀ y, curveSpeed F (fun z _ => gamma (sigma.symm z)) t y = 1) ∧
      (∀ y, (curveSpeed F (fun z _ => gamma (sigma.symm z)) t y ^ 2)⁻¹ = 1) ∧
      ∀ x, gamma (sigma.symm (sigma x)) = gamma x := by
  let v := curveSpeed F (fun x _ => gamma x) t
  let ell := ∫ x in (0 : ℝ)..curvePeriod, v x
  have hp : 0 < curvePeriod := Real.two_pi_pos
  obtain ⟨hell, phi, hformula, hphi, hinv, hzero, hdpos, hinvpos, hshift, hinvshift,
    _, hq, _, hspeed, _⟩ :=
    exists_c2_constant_speed_relabeling F gamma t hperiod hgamma himm
  change 0 < ell at hell
  change ∀ x, phi x = (curvePeriod / ell) * ∫ y in (0 : ℝ)..x, v y at hformula
  change ∀ y, curveSpeed F (fun z _ => gamma (phi.symm z)) t y =
    ell / curvePeriod at hspeed
  let c : ℝ := ell / curvePeriod
  have hc : 0 < c := div_pos hell hp
  let sigma : ℝ ≃ₜ ℝ := phi.trans (Homeomorph.mulLeft₀ c hc.ne')
  have hsig (x : ℝ) : sigma x = c * phi x := rfl
  have hsigInv (y : ℝ) : sigma.symm y = phi.symm ((curvePeriod / ell) * y) := by
    change phi.symm (c⁻¹ * y) = _
    dsimp only [c]
    rw [inv_div]
  have hsigFun : (sigma : ℝ → ℝ) = fun x => c * phi x := funext hsig
  have hsigInvFun : (sigma.symm : ℝ → ℝ) =
      fun y => phi.symm ((curvePeriod / ell) * y) := funext hsigInv
  have hscale : 0 < curvePeriod / ell := div_pos hp hell
  have hsigReg : ContDiff ℝ 2 (sigma : ℝ → ℝ) := by
    rw [hsigFun]
    exact contDiff_const.mul hphi
  have hsigInvReg : ContDiff ℝ 2 (sigma.symm : ℝ → ℝ) := by
    rw [hsigInvFun]
    exact hinv.comp (contDiff_const.mul contDiff_id)
  have hsigPos (x : ℝ) : 0 < deriv sigma x := by
    have hd := ((hphi.differentiable (by norm_num) x).hasDerivAt.const_mul c)
    rw [hsigFun, hd.deriv]
    exact mul_pos hc (hdpos x)
  have hsigInvPos (y : ℝ) : 0 < deriv sigma.symm y := by
    have hd := ((hinv.differentiable (by norm_num)
      ((curvePeriod / ell) * y)).hasDerivAt).comp y
        ((hasDerivAt_id y).const_mul (curvePeriod / ell))
    simp only [Function.comp_def, mul_one] at hd
    rw [hsigInvFun, hd.deriv]
    exact mul_pos (hinvpos _) hscale
  have hsigShift (x : ℝ) : sigma (x + curvePeriod) = sigma x + ell := by
    rw [hsig, hshift, hsig]
    dsimp only [c]
    field_simp
  have hsigInvShift (y : ℝ) : sigma.symm (y + ell) = sigma.symm y + curvePeriod := by
    rw [hsigInv, hsigInv]
    have heq : (curvePeriod / ell) * (y + ell) = (curvePeriod / ell) * y + curvePeriod := by
      field_simp [hell.ne']
    rw [heq, hinvshift]
  have hnewSpeed (y : ℝ) :
      curveSpeed F (fun z _ => gamma (sigma.symm z)) t y = 1 := by
    simp only [hsigInvFun]
    calc
      _ = (curvePeriod / ell) *
          curveSpeed F (fun z _ => gamma (phi.symm z)) t ((curvePeriod / ell) * y) :=
        curveSpeed_comp F (fun z _ => gamma (phi.symm z))
          (hq.mdifferentiable (by norm_num) _)
          (by simpa only [id_eq, mul_one] using
            (hasDerivAt_id y).const_mul (curvePeriod / ell)) hscale.le
      _ = 1 := by rw [hspeed]; field_simp [hell.ne']
  refine ⟨hell, sigma, ?_, hsigReg, hsigInvReg, ?_, hsigPos, hsigInvPos,
    hsigShift, hsigInvShift, ?_, hgamma.comp hsigInvReg.contMDiff, ?_, hnewSpeed, ?_, ?_⟩
  · intro x
    change sigma x = ∫ y in (0 : ℝ)..x, v y
    rw [hsig, hformula]
    dsimp only [c]
    field_simp
  · rw [hsig, hzero, mul_zero]
  · intro y
    dsimp only
    rw [hsigInvShift, hperiod]
  · intro y
    rw [curveVelocity_comp (hgamma.mdifferentiable (by norm_num) _)
      ((hsigInvReg.differentiable (by norm_num) y).hasDerivAt)]
    exact smul_ne_zero (hsigInvPos y).ne' (himm _)
  · intro y
    rw [hnewSpeed]
    norm_num
  · intro x
    rw [sigma.symm_apply_apply]

end PoincareConjecture.M63
