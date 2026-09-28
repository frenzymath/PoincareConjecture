import PoincareConjecture.Proofs.M10.BranchCalculus
import PoincareConjecture.Proofs.M10.NoncriticalOpen

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y]

theorem eventually_hasDerivAt_actionBranchPhase
    {E : X × ℝ → Y} {A : X × ℝ → ℝ}
    {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {R : Y × ℝ → ℝ} {z : X × ℝ}
    (hE : ContDiffAt ℝ ∞ E z) (hA : ContDiffAt ℝ ∞ A z)
    (hB : ContDiffAt ℝ ∞ B (E z, z.2)) (hR : ContDiffAt ℝ ∞ R (E z, z.2))
    (ht : 0 < z.2) (hi : (B (E z, z.2)).IsInvertible)
    (hsym : ∀ᶠ w in 𝓝 (E z, z.2), ∀ u v : Y, B w u v = B w v u)
    (hspace : ∀ᶠ w in 𝓝 z, ∀ h : X,
      fderiv ℝ A w (h, 0) = actionBranchMomentum E B w (fderiv ℝ E w (h, 0)))
    (htime : ∀ᶠ w in 𝓝 z,
      fderiv ℝ A w (0, 1) = kineticLagrangian B R
        (w.2, E w, fderiv ℝ E w (0, 1)))
    (hcrit : Function.Bijective (fun h : X ↦ fderiv ℝ E z (h, 0))) :
    ∀ᶠ t in 𝓝 z.2, HasDerivAt (actionBranchPhase E B z.1)
      (phaseField B R (actionBranchPhase E B z.1 t)) t := by
  have hP := actionBranchMomentum_contDiffAt hE hB ht
  have hH : ContinuousAt (fun w : X × ℝ ↦ (E w, w.2)) z :=
    hE.continuousAt.prodMk continuous_snd.continuousAt
  have hV : ContDiffAt ℝ ∞ (fun w : X × ℝ ↦ fderiv ℝ E w (0, 1)) z :=
    (hE.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hC : ContinuousAt
      (fun w : X × ℝ ↦ (w.2, E w, fderiv ℝ E w (0, 1))) z :=
    continuous_snd.continuousAt.prodMk (hE.continuousAt.prodMk hV.continuousAt)
  have hL : ContDiffAt ℝ 1 (kineticLagrangian B R)
      (z.2, E z, fderiv ℝ E z (0, 1)) :=
    kineticLagrangian_contDiffAt (hB.of_le (by simp)) (hR.of_le (by simp)) ht
  have hbij : ∀ᶠ w in 𝓝 z,
      Function.Bijective ((fderiv ℝ E w).comp (ContinuousLinearMap.inl ℝ X ℝ)) :=
    eventually_bijective_of_continuousAt
      (((hE.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const).continuousAt) hcrit
  have hinv' : ∀ᶠ w in 𝓝 (E z, z.2), (B w).IsInvertible :=
    hB.continuousAt (ContinuousLinearEquiv.isOpen.mem_nhds hi)
  have hinv : ∀ᶠ w in 𝓝 z, (B (E w, w.2)).IsInvertible := hH hinv'
  have hall : ∀ᶠ w in 𝓝 z, HasDerivAt (actionBranchPhase E B w.1)
      (phaseField B R (actionBranchPhase E B w.1 w.2)) w.2 := by
    filter_upwards [(hE.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually
        (by norm_num),
      (hA.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by norm_num),
      (hP.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp),
      hC (hL.eventually (by simp)), continuous_snd.continuousAt (eventually_gt_nhds ht),
      hinv, hH hsym, hspace.eventually_nhds, htime.eventually_nhds, hbij]
      with w hwE hwA hwP hwL hwt hwi hwsym hwspace hwtime hwbij
    change ContDiffAt ℝ 1 (kineticLagrangian B R)
      (w.2, E w, fderiv ℝ E w (0, 1)) at hwL
    exact hasDerivAt_actionBranchPhase hwE hwA (hwP.differentiableAt one_ne_zero)
      (hwL.differentiableAt one_ne_zero) hwt hwi hwsym hwspace hwtime hwbij.2
  exact (continuousAt_const.prodMk continuousAt_id) hall

end PoincareConjecture.M10
