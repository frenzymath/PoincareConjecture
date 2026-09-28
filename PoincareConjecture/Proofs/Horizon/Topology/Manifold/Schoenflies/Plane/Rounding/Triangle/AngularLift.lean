import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle.Equilateral
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicFiber









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane


theorem hasDerivAt_rotatingArgument {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (a : ℝ)
    (hdom : γ t * (Circle.exp (-(a * t)) : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun s => a * s + Complex.arg (γ s * (Circle.exp (-(a * s)) : ℂ)))
      (v / γ t).im t := by
  let e : ℂ := Circle.exp (-(a * t))
  have he : e ≠ 0 := Circle.coe_ne_zero _
  have hγ0 : γ t ≠ 0 := (mul_ne_zero_iff.mp (Complex.slitPlane_ne_zero hdom)).1
  have hphase : HasDerivAt (fun s => (Circle.exp (-(a * s)) : ℂ))
      (e * (-(a : ℂ) * Complex.I)) t := by
    simpa only [Circle.coe_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_one, mul_one, e, Pi.neg_apply, id_eq] using
      ((((hasDerivAt_id t).const_mul a).neg.ofReal_comp).mul_const Complex.I).cexp
  have hprod := hγ.mul hphase
  have hlog := hprod.clog_real hdom
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  have hsum := ((hasDerivAt_id t).const_mul a).add him
  have hquot : (v * e + γ t * (e * (-(a : ℂ) * Complex.I))) / (γ t * e) =
      v / γ t - (a : ℂ) * Complex.I := by
    field_simp
    ring
  have hd : a + ((v * e + γ t * (e * (-(a : ℂ) * Complex.I))) / (γ t * e)).im =
      (v / γ t).im := by
    rw [hquot]
    simp
  convert! hsum using 1
  · funext s
    simp [Complex.log_im]
  · simpa only [Complex.imCLM_apply, Pi.mul_apply, mul_one] using hd.symm


theorem hasDerivAt_equilateralCorner {ρ : ℝ → ℝ} {s : ℝ}
    (hρ : DifferentiableAt ℝ ρ s) :
    HasDerivAt (equilateralCorner ρ)
      (((-3 * deriv ρ s / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) s := by
  have hre := (((hρ.hasDerivAt.const_mul 3).div_const 2).const_sub 1).ofReal_comp
  have him := (((hasDerivAt_id s).const_mul (Real.sqrt 3)).div_const 2).ofReal_comp
  convert! hre.add (him.mul_const Complex.I) using 1
  push_cast
  ring


theorem equilateralCorner_logDeriv_im_pos {ρ : ℝ → ℝ} {δ s : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : DifferentiableAt ℝ ρ s) (hder : ∀ t, |deriv ρ t| ≤ 1)
    (hs : |s| ≤ 1 / 2) :
    0 < (deriv (equilateralCorner ρ) s / equilateralCorner ρ s).im := by
  have hreal := equilateralCorner_re_pos (by linarith) htail hbound hs
  have hz : equilateralCorner ρ s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hreal
    exact (lt_irrefl 0) hreal
  have hn : 0 < Complex.normSq (equilateralCorner ρ s) := Complex.normSq_pos.mpr hz
  have hfactor := roundedCorner_radial_factor_pos hδ hδsmall htail hbound hder s
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [(hasDerivAt_equilateralCorner hρ).deriv, Complex.div_im, ← sub_div]
  apply div_pos _ hn
  simp only [equilateralCorner, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.add_re, Complex.mul_re,
    mul_zero, mul_one, add_zero, zero_add, sub_zero]
  nlinarith [mul_pos hsqrt hfactor]



theorem deriv_roundedEquilateralAngle_pos {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ t, |deriv ρ t| ≤ 1) (t : ℝ) :
    0 < deriv (roundedEquilateralAngle ρ) t := by
  let j : ℤ := ⌊t + 1 / 2⌋
  have hjlo : (j : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hjhi : t + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hs : |t - (j : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hactual := hasDerivAt_roundedVertexPath equilateralVertex hδ (by linarith)
    htail hbound hρ t
  have hdom : roundedVertexPath ρ equilateralVertex t *
      (Circle.exp (-(2 * Real.pi / 3 * t)) : ℂ) ∈ Complex.slitPlane :=
    Or.inl (roundedEquilateral_rotating_re_pos (by linarith) htail hbound t)
  have hangle := hasDerivAt_rotatingArgument hactual.differentiableAt.hasDerivAt
    (2 * Real.pi / 3) hdom
  change HasDerivAt (roundedEquilateralAngle ρ) _ t at hangle
  rw [hangle.deriv]
  have hcorner : roundedCorner ρ (equilateralVertex j)
      (equilateralVertex j - equilateralVertex (j - 1))
      (equilateralVertex (j + 1) - equilateralVertex j) =
      fun s => equilateralVertex j * equilateralCorner ρ s :=
    funext (roundedCorner_equilateral_eq ρ j)
  have hcentral := hasDerivAt_equilateralCorner (hρ (t - j))
  have hcentral' := hcentral.congr_deriv hcentral.deriv.symm
  have hvelocity : deriv (roundedVertexPath ρ equilateralVertex) t =
      equilateralVertex j * deriv (equilateralCorner ρ) (t - j) := by
    rw [hactual.deriv]
    change deriv (roundedCorner ρ (equilateralVertex j)
      (equilateralVertex j - equilateralVertex (j - 1))
      (equilateralVertex (j + 1) - equilateralVertex j)) (t - j) = _
    rw [hcorner]
    exact (hcentral'.const_mul (equilateralVertex j)).deriv
  rw [hvelocity, roundedVertexPath_equilateral_eq]
  change 0 < ((equilateralVertex j * deriv (equilateralCorner ρ) (t - j)) /
    (equilateralVertex j * equilateralCorner ρ (t - j))).im
  rw [mul_div_mul_left _ _ (show equilateralVertex j ≠ 0 from Circle.coe_ne_zero _)]
  exact equilateralCorner_logDeriv_im_pos hδ hδsmall htail hbound (hρ _) hder hs



theorem exists_smooth_inverse_roundedEquilateralAngle {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ t, |deriv ρ t| ≤ 1) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧
      (∀ s, roundedEquilateralAngle ρ (β s) = s) ∧
      (∀ t, β (roundedEquilateralAngle ρ t) = t) ∧
      ∀ s, β (s + 2 * Real.pi) = β s + 3 := by
  let c : ℝ := 3 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  have hα := contDiff_roundedEquilateralAngle hδ (by linarith) htail hbound hρ
  let F : ℝ × ℝ → ℝ := fun p => c * roundedEquilateralAngle ρ p.2
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul (hα.comp contDiff_snd)
  have hper (z t : ℝ) : F (z, t + 3) = F (z, t) + 3 := by
    dsimp only [F]
    rw [roundedEquilateralAngle_add_three]
    dsimp [c]
    field_simp
  have hpos (z t : ℝ) : 0 < deriv (fun s => F (z, s)) t := by
    have hd := ((hα.differentiable (by simp) t).hasDerivAt.const_mul c).deriv
    change deriv (fun s => c * roundedEquilateralAngle ρ s) t = _ at hd
    change 0 < deriv (fun s => c * roundedEquilateralAngle ρ s) t
    rw [hd]
    exact mul_pos hc (deriv_roundedEquilateralAngle_pos hδ hδsmall htail hbound
      (hρ.differentiable (by simp)) hder t)
  obtain ⟨G, hG, hi⟩ := exists_smooth_inverse_of_add_period (by norm_num : (0 : ℝ) < 3)
    hF hper hpos
  let β : ℝ → ℝ := fun s => G (0, c * s)
  have hβ : ContDiff ℝ ∞ β := hG.comp (contDiff_const.prodMk (contDiff_const.mul contDiff_id))
  refine ⟨β, hβ, ?_, ?_, ?_⟩
  · intro s
    have h := (hi 0 (c * s)).1
    change c * roundedEquilateralAngle ρ (β s) = c * s at h
    exact mul_left_cancel₀ hc.ne' h
  · intro t
    exact (hi 0 t).2.1
  · intro s
    have hscale : c * (s + 2 * Real.pi) = c * s + 3 := by
      dsimp [c]
      field_simp
    change G (0, c * (s + 2 * Real.pi)) = G (0, c * s) + 3
    rw [hscale]
    exact (hi 0 (c * s)).2.2



theorem norm_mul_exp_rotatingArgument (z : ℂ) (a : ℝ) :
    (‖z‖ : ℂ) * (Circle.exp (a + Complex.arg (z * (Circle.exp (-a) : ℂ))) : ℂ) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I (z * (Circle.exp (-a) : ℂ))
  have hn : ‖z * (Circle.exp (-a) : ℂ)‖ = ‖z‖ := by rw [norm_mul, Circle.norm_coe, mul_one]
  rw [hn] at h
  change (‖z‖ : ℂ) * (Circle.exp (Complex.arg (z * (Circle.exp (-a) : ℂ))) : ℂ) =
    z * (Circle.exp (-a) : ℂ) at h
  rw [Circle.exp_add, Circle.coe_mul, mul_left_comm, h, mul_left_comm,
    ← Circle.coe_mul, ← Circle.exp_add]
  simp

end Poincare.Manifold.Schoenflies.Plane
