import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace Poincare.ODE.LocalFlow



theorem exists_vertical_field_connector
    {r R h a b : ℝ} (hr : 0 < r) (hrR : r < R) (hh : 0 < h)
    (ha : |a| ≤ r) (hb : |b| ≤ r) :
    ∃ (W : ℝ × ℝ → ℝ × ℝ) (γ : ℝ → ℝ × ℝ),
      ContDiff ℝ ∞ W ∧ ContDiff ℝ ∞ γ ∧
      (∀ z, (W z).2 = 1) ∧
      (∀ z, R ≤ |z.1| ∨ h ≤ |z.2| → W z = (0, 1)) ∧
      (∀ t, HasDerivAt γ (W (γ t)) t) ∧
      (∀ t, (γ t).2 = t ∧ |(γ t).1| ≤ r) ∧
      (∀ t, t ≤ -h → γ t = (b, t)) ∧
      (∀ t, h ≤ t → γ t = (a, t)) := by
  let θ : ℝ → ℝ := fun t => Real.smoothTransition (t / h + 1 / 2)
  have hθ : ContDiff ℝ ∞ θ := Real.smoothTransition.contDiff.comp
    ((contDiff_id.div_const h).add contDiff_const)
  have hθlo (t : ℝ) (ht : t < -h / 2) : θ t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have : t / h < -(1 / 2 : ℝ) := (div_lt_iff₀ hh).mpr (by linarith)
    linarith
  have hθhi (t : ℝ) (ht : h / 2 < t) : θ t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have : (1 / 2 : ℝ) < t / h := (lt_div_iff₀ hh).mpr (by linarith)
    linarith
  let u : ℝ → ℝ := fun t => b + (a - b) * θ t
  have hu : ContDiff ℝ ∞ u := contDiff_const.add (contDiff_const.mul hθ)
  have hubound (t : ℝ) : |u t| ≤ r := by
    have ht0 : 0 ≤ θ t := Real.smoothTransition.nonneg _
    have ht1 : θ t ≤ 1 := Real.smoothTransition.le_one _
    obtain ⟨ha0, ha1⟩ := abs_le.mp ha
    obtain ⟨hb0, hb1⟩ := abs_le.mp hb
    dsimp only [u]
    rw [abs_le]
    constructor <;> nlinarith
  have hulo (t : ℝ) (ht : t < -h / 2) : u t = b := by simp [u, hθlo t ht]
  have huhi (t : ℝ) (ht : h / 2 < t) : u t = a := by simp [u, hθhi t ht]
  have hduzero (t : ℝ) (ht : h ≤ |t|) : deriv u t = 0 := by
    rcases le_abs.mp ht with ht | ht
    · have hlt : h / 2 < t := by linarith
      have heq : u =ᶠ[𝓝 t] fun _ => a := by
        filter_upwards [eventually_gt_nhds hlt] with s hs
        exact huhi s hs
      exact heq.deriv_eq.trans (deriv_const t a)
    · have hlt : t < -h / 2 := by linarith
      have heq : u =ᶠ[𝓝 t] fun _ => b := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        exact hulo s hs
      exact heq.deriv_eq.trans (deriv_const t b)
  let χ : ContDiffBump (0 : ℝ) := ⟨r, R, hr, hrR⟩
  have hχu (t : ℝ) : χ (u t) = 1 := χ.one_of_mem_closedBall
    (by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hubound t)
  let W : ℝ × ℝ → ℝ × ℝ := fun z => (χ z.1 * deriv u z.2, 1)
  let γ : ℝ → ℝ × ℝ := fun t => (u t, t)
  refine ⟨W, γ, ?_, hu.prodMk contDiff_id, fun _ => rfl, ?_, ?_,
    fun t => ⟨rfl, hubound t⟩, ?_, ?_⟩
  · exact ((χ.contDiff.comp contDiff_fst).mul
      ((contDiff_infty_iff_deriv.mp hu).2.comp contDiff_snd)).prodMk contDiff_const
  · intro z hz
    rcases hz with hz | hz
    · have hc : χ z.1 = 0 := χ.zero_of_le_dist (by simpa [Real.dist_eq] using hz)
      simp [W, hc]
    · simp [W, hduzero z.2 hz]
  · intro t
    simpa only [W, γ, hχu, one_mul, id_eq] using
      ((hu.differentiable (by simp) t).hasDerivAt.prodMk (hasDerivAt_id t))
  · intro t ht
    exact Prod.ext (hulo t (by linarith)) rfl
  · intro t ht
    exact Prod.ext (huhi t (by linarith)) rfl

end Poincare.ODE.LocalFlow
