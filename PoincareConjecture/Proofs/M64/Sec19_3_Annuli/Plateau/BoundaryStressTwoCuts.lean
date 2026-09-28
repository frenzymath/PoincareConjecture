import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryStressMoments
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnBoundary
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicCircleShift












set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "a" => curvePeriod / 2
local notation "T" => m64AnnulusHalfTurn

private theorem stress_integrable {U V : LoopPlane → ℝ}
    (hU : Integrable U mu) (hV : Integrable V mu)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta) (hrho : ContDiff ℝ ∞ rho) :
    Integrable (fun p : LoopPlane => deriv eta (p 0) * rho (p 1) * U p +
      eta (p 0) * deriv rho (p 1) * V p) mu := by
  have hc0 : Continuous (fun p : LoopPlane => deriv eta (p 0) * rho (p 1)) :=
    ((heta.continuous_deriv (by simp)).comp (EuclideanSpace.proj 0).continuous).mul
      (hrho.continuous.comp (EuclideanSpace.proj 1).continuous)
  have hc1 : Continuous (fun p : LoopPlane => eta (p 0) * deriv rho (p 1)) :=
    (heta.continuous.comp (EuclideanSpace.proj 0).continuous).mul
      ((hrho.continuous_deriv (by simp)).comp (EuclideanSpace.proj 1).continuous)
  exact (m64Annulus_continuous_mul_integrable hU hc0).add
    (m64Annulus_continuous_mul_integrable hV hc1)




theorem m64LocalizedStress_halfTurn
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) (hrho : ContDiff ℝ ∞ rho) :
    (∫ p in S, deriv (fun x => eta (x + a)) (p 0) * rho (p 1) * U (T p) +
      eta (p 0 + a) * deriv rho (p 1) * V (T p)) =
      ∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p := by
  have hshift {f : ℝ → ℝ} (hf : Function.Periodic f curvePeriod) (p : LoopPlane) :
      f (p 0 + a) = f (T p 0) := by
    dsimp only [m64AnnulusHalfTurn]
    split_ifs with hp
    · rfl
    · change f (p 0 + a) = f (p 0 - a)
      rw [show p 0 + a = (p 0 - a) + curvePeriod by ring, hf]
  have hsecond (p : LoopPlane) : T p 1 = p 1 := by
    dsimp only [m64AnnulusHalfTurn]
    split_ifs <;> simp [annulusPoint]
  calc
    _ = ∫ p in S, deriv eta (T p 0) * rho (T p 1) * U (T p) +
        eta (T p 0) * deriv rho (T p 1) * V (T p) := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [deriv_comp_add_const, hshift (m64Periodic_deriv hperiod), hshift hperiod,
        hsecond]
    _ = _ := m64AnnulusHalfTurn_integral_comp
      (stress_integrable hU hV heta hrho).aestronglyMeasurable




theorem m64LocalizedStress_of_two_cuts
    {U V : LoopPlane → ℝ} (hU : Integrable U mu) (hV : Integrable V mu)
    {rho : ℝ → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hzero : ∀ eta : ℝ → ℝ, ContDiff ℝ ∞ eta →
      Function.Periodic eta curvePeriod → eta 0 = 0 →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p) = 0)
    (hhalf : ∀ eta : ℝ → ℝ, ContDiff ℝ ∞ eta →
      Function.Periodic eta curvePeriod → eta a = 0 →
      (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
        eta (p 0) * deriv rho (p 1) * V p) = 0)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) :
    (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
      eta (p 0) * deriv rho (p 1) * V p) = 0 := by
  let psi : ℝ → ℝ := fun x => (1 + Real.cos x) / 2
  have hs : ContDiff ℝ ∞ psi := (contDiff_const.add Real.contDiff_cos).div_const 2
  have hp : Function.Periodic psi curvePeriod := by
    intro x
    dsimp only [psi, curvePeriod]
    rw [Real.cos_periodic x]
  have hz : psi 0 = 1 := by norm_num [psi]
  have ha : psi a = 0 := by norm_num [psi, curvePeriod]
  let eta1 : ℝ → ℝ := fun x => eta 0 * psi x
  let eta0 : ℝ → ℝ := fun x => eta x - eta1 x
  have h1s : ContDiff ℝ ∞ eta1 := contDiff_const.mul hs
  have h0s : ContDiff ℝ ∞ eta0 := heta.sub h1s
  have h1p : Function.Periodic eta1 curvePeriod := fun x => by
    dsimp only [eta1]
    rw [hp]
  have h0p : Function.Periodic eta0 curvePeriod := fun x => by
    dsimp only [eta0]
    rw [hperiod, h1p]
  have h0 := hzero eta0 h0s h0p (by simp only [eta0, eta1, hz, mul_one, sub_self])
  have h1 := hhalf eta1 h1s h1p (by simp only [eta1, ha, mul_zero])
  have heq (x : ℝ) : eta x = eta0 x + eta1 x := by dsimp only [eta0]; ring
  have hd (x : ℝ) : deriv eta x = deriv eta0 x + deriv eta1 x := by
    have hf : eta = fun x => eta0 x + eta1 x := funext heq
    rw [hf]
    exact ((h0s.differentiable (by simp) x).hasDerivAt.add
      (h1s.differentiable (by simp) x).hasDerivAt).deriv
  have hsplit : (∫ p in S, deriv eta (p 0) * rho (p 1) * U p +
      eta (p 0) * deriv rho (p 1) * V p) =
      (∫ p in S, deriv eta0 (p 0) * rho (p 1) * U p +
        eta0 (p 0) * deriv rho (p 1) * V p) +
      (∫ p in S, deriv eta1 (p 0) * rho (p 1) * U p +
        eta1 (p 0) * deriv rho (p 1) * V p) := by
    rw [← integral_add (stress_integrable hU hV h0s hrho)
      (stress_integrable hU hV h1s hrho)]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [hd, heq]
    ring
  rw [hsplit, h0, h1, add_zero]

end PoincareConjecture
