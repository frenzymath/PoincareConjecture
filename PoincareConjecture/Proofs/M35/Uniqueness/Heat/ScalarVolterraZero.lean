import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongRecovery
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat

theorem scalar_homogeneous_integral_zero {T c : ℝ} (hT : 0 < T)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, q t = ∫ s in (0 : ℝ)..t, c * q s) :
    ∀ t ∈ Icc 0 T, q t = 0 := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt q (c * q t) (Icc 0 T) t := by
    have hp := hasDerivWithinAt_volterraPath_Icc (x₀ := (0 : ℝ)) (hq.const_mul c) ht
    apply hp.congr_of_mem ?_ ht
    intro s hs
    simpa only [volterraPath, zero_add] using heq s hs
  let z : ℝ → ℝ := fun t => Real.exp (-c * t) * q t
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt z 0 (Icc 0 T) t := by
    have he := ((hasDerivAt_id t).const_mul (-c)).exp
    have hp : HasDerivWithinAt z
        ((Real.exp (-c * t) * -c) * q t + Real.exp (-c * t) * (c * q t)) (Icc 0 T) t := by
      simpa only [z, id_eq, mul_one, Pi.mul_apply] using! he.hasDerivWithinAt.mul (hd t ht)
    exact hp.congr_deriv (by ring)
  have hconst := constant_of_derivWithin_zero
    (fun t ht => (hz t ht).differentiableWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).derivWithin
      ((uniqueDiffOn_Icc hT) t (Ico_subset_Icc_self ht)))
  have hq0 : q 0 = 0 := by
    simpa only [intervalIntegral.integral_same] using heq 0 ⟨le_rfl, hT.le⟩
  intro t ht
  have he := hconst t ht
  change Real.exp (-c * t) * q t = Real.exp (-c * 0) * q 0 at he
  rw [hq0, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (Real.exp_ne_zero _)

end PoincareConjecture.M35.Uniqueness.Heat
