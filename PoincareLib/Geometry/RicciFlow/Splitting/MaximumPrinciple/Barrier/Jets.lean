import PoincareLib.Geometry.RicciFlow.Splitting.MaximumPrinciple.Barrier.MovingBump

/-!
# Actual first and second derivatives of the moving bump

All formulas hold across the moving support boundary. The center path needs
only the indicated actual time derivative. Spatial differentiation uses the
same function and the ordinary Frechet derivative in the coordinate space.
-/

noncomputable section
open scoped InnerProductSpace ContDiff

namespace PoincareMT.RicciFlow.Splitting.MaximumPrinciple.Barrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual first time derivative, expressed using the center velocity. -/
def timeJet (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x velocity : E) : ℝ :=
  Real.exp (-C * (t - a)) *
    (-C * expNegInvGlue (ballGap rho (gamma t) x) +
      profileFirst (ballGap rho (gamma t) x) * (2 * ⟪x - gamma t, velocity⟫_ℝ))

/-- The first spatial derivative in direction `u`. -/
def spaceJet (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x u : E) : ℝ :=
  Real.exp (-C * (t - a)) *
    (profileFirst (ballGap rho (gamma t) x) * (-2 * ⟪x - gamma t, u⟫_ℝ))

/-- The mixed spatial derivative, with first direction `u` and second `w`. -/
def secondSpaceJet (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x u w : E) : ℝ :=
  Real.exp (-C * (t - a)) *
    (4 * profileSecond (ballGap rho (gamma t) x) *
        ⟪x - gamma t, u⟫_ℝ * ⟪x - gamma t, w⟫_ℝ -
      2 * profileFirst (ballGap rho (gamma t) x) * ⟪w, u⟫_ℝ)

/-- Differentiating the actual translated squared radius in time. -/
theorem hasDerivAt_ballGap_time (rho : ℝ) {gamma : ℝ → E}
    {t : ℝ} {velocity : E} (hg : HasDerivAt gamma velocity t) (x : E) :
    HasDerivAt (fun s => ballGap rho (gamma s) x)
      (2 * ⟪x - gamma t, velocity⟫_ℝ) t := by
  have h := (hasDerivAt_const t (rho ^ 2)).sub
    (((hasDerivAt_const t x).sub hg).norm_sq)
  simpa [ballGap] using! h

/-- The actual time derivative, including at the support boundary. -/
theorem hasDerivAt_movingBump_time (rho C a : ℝ) {gamma : ℝ → E}
    {t : ℝ} {velocity : E} (hg : HasDerivAt gamma velocity t) (x : E) :
    HasDerivAt (fun s => movingBump rho C a gamma s x)
      (timeJet rho C a gamma t x velocity) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-C * (s - a)))
      (-C * Real.exp (-C * (t - a))) t := by
    simpa [mul_comm] using! (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp
  have hp := (hasDerivAt_profile (ballGap rho (gamma t) x)).comp t
    (hasDerivAt_ballGap_time rho hg x)
  convert! he.mul hp using 1
  dsimp [timeJet]
  ring

/-- First spatial differentiation along an actual differentiable coordinate curve. -/
theorem hasDerivAt_movingBump_along (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ)
    {eta : ℝ → E} {r : ℝ} {u : E} (he : HasDerivAt eta u r) :
    HasDerivAt (fun s => movingBump rho C a gamma t (eta s))
      (spaceJet rho C a gamma t (eta r) u) r := by
  have hq : HasDerivAt (fun s => ballGap rho (gamma t) (eta s))
      (-2 * ⟪eta r - gamma t, u⟫_ℝ) r := by
    simpa [ballGap] using! (hasDerivAt_const r (rho ^ 2)).sub
      ((he.sub_const (gamma t)).norm_sq)
  have hp := (hasDerivAt_profile (ballGap rho (gamma t) (eta r))).comp r hq
  exact hp.const_mul (Real.exp (-C * (t - a)))

/-- Mixed second spatial differentiation along a differentiable coordinate curve. -/
theorem hasDerivAt_spaceJet_along (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ)
    (u : E) {eta : ℝ → E} {r : ℝ} {w : E} (he : HasDerivAt eta w r) :
    HasDerivAt (fun s => spaceJet rho C a gamma t (eta s) u)
      (secondSpaceJet rho C a gamma t (eta r) u w) r := by
  have hq : HasDerivAt (fun s => ballGap rho (gamma t) (eta s))
      (-2 * ⟪eta r - gamma t, w⟫_ℝ) r := by
    simpa [ballGap] using! (hasDerivAt_const r (rho ^ 2)).sub
      ((he.sub_const (gamma t)).norm_sq)
  have hp := (hasDerivAt_profileFirst (ballGap rho (gamma t) (eta r))).comp r hq
  have hi := ((he.sub_const (gamma t)).inner ℝ (hasDerivAt_const r u)).const_mul (-2)
  convert! (hp.mul hi).const_mul (Real.exp (-C * (t - a))) using 1
  simp only [secondSpaceJet, inner_zero_right, Function.comp_apply, zero_add]
  ring

/-- The first jet is the actual Frechet derivative in every direction. -/
theorem fderiv_movingBump (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x u : E) :
    fderiv ℝ (movingBump rho C a gamma t) x u = spaceJet rho C a gamma t x u := by
  have hl : HasDerivAt (fun s : ℝ => x + s • u) u 0 := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const u)
  have hactual := (contDiff_movingBump_space rho C a gamma t).differentiable
    (by simp) |>.differentiableAt (x := x) |>.hasFDerivAt
  have hcompose := hactual.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hexplicit := hasDerivAt_movingBump_along rho C a gamma t hl
  simpa using hcompose.unique hexplicit

/-- Smoothness of the first jet in its base point. -/
theorem contDiff_spaceJet (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (u : E) :
    ContDiff ℝ ∞ (fun x => spaceJet rho C a gamma t x u) := by
  have heq : (fun x => spaceJet rho C a gamma t x u) =
      fun x => fderiv ℝ (movingBump rho C a gamma t) x u := by
    funext x
    exact (fderiv_movingBump rho C a gamma t x u).symm
  rw [heq]
  exact ((contDiff_movingBump_space rho C a gamma t).fderiv_right
    (by simp)).clm_apply contDiff_const

/-- The second jet is the actual derivative of the first directional derivative. -/
theorem fderiv_spaceJet (rho C a : ℝ) (gamma : ℝ → E) (t : ℝ) (x u w : E) :
    fderiv ℝ (fun y => fderiv ℝ (movingBump rho C a gamma t) y u) x w =
      secondSpaceJet rho C a gamma t x u w := by
  simp_rw [fderiv_movingBump]
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hactual := (contDiff_spaceJet rho C a gamma t u).differentiable
    (by simp) |>.differentiableAt (x := x) |>.hasFDerivAt
  have hcompose := hactual.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hexplicit := hasDerivAt_spaceJet_along rho C a gamma t u hl
  simpa using hcompose.unique hexplicit

end PoincareMT.RicciFlow.Splitting.MaximumPrinciple.Barrier

