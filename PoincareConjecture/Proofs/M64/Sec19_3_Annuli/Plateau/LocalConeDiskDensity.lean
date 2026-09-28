import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeDiskColumns
import PoincareConjecture.Proofs.M58.Cor18_28_AreaBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

open Proofs.M58

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64LocalConeDiskMap_energy_zero_of_inner (g : RiemannianMetric n M)
    (H : ℝ × (M × M) → M) (center : M) (gamma : ℝ → M)
    (h0 : ∀ x, H (0, center, gamma x) = center)
    {z : LoopPlane} (hz : ‖z‖ < 1 / 2) :
    m60EnergyDensity g (m64LocalConeDiskMap H center gamma) z = 0 := by
  have heq : m64LocalConeDiskMap H center gamma =ᶠ[𝓝 z] (fun _ => center) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact m64LocalConeDiskMap_inner H center gamma h0 hw.le
  have hd := heq.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 n)
  simp only [m60EnergyDensity, Matrix.trace_fin_two, m60AreaGram, hd,
    mfderiv_const, zero_apply, map_zero, add_zero, mul_zero]

theorem m64LocalConeDiskMap_polar_energy_le (g : RiemannianMetric n M)
    (H : ℝ × (M × M) → M) (center : M) (gamma : ℝ → M)
    (hperiod : Function.Periodic gamma curvePeriod)
    (h0 : ∀ x, H (0, center, gamma x) = center)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (t : ℝ) {B P : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma t)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 n)
      (m64LocalConeDiskMap H center gamma) (r • angularPoint t))
    (hH : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
      (1 - diskTimeProfile r, center, gamma t))
    (hspeed : g.tangentNorm (H (1 - diskTimeProfile r, center, gamma t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, center, gamma t))
        (1 - diskTimeProfile r) 1) = (g.edist center (gamma t)).toReal)
    (hlast : ∀ v : TangentSpace (𝓡 n) (gamma t),
      g.tangentNorm (H (1 - diskTimeProfile r, center, gamma t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
          (1 - diskTimeProfile r, center, gamma t) (0, 0, v)) ≤
            B * g.tangentNorm (gamma t) v)
    (hprofile : |deriv diskTimeProfile r| ≤ P) :
    r * m60EnergyDensity g (m64LocalConeDiskMap H center gamma) (r • angularPoint t) ≤
      P ^ 2 / 2 * (g.edist center (gamma t)).toReal ^ 2 +
        2 * B ^ 2 * (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F := m64LocalConeDiskMap H center gamma
  have hn : ‖r • angularPoint t‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularPoint, mul_one]
  by_cases hsmall : r < 1 / 2
  · rw [m64LocalConeDiskMap_energy_zero_of_inner g H center gamma h0 (by rwa [hn]),
      mul_zero]
    positivity
  have hhalf : 1 / 2 ≤ r := le_of_not_gt hsmall
  have hslice : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s => H (s, center, gamma t)) (1 - diskTimeProfile r) := by
    have hi : MDifferentiableAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n)))
        (fun s : ℝ => (s, center, gamma t)) (1 - diskTimeProfile r) :=
      mdifferentiableAt_id.prodMk (mdifferentiableAt_const.prodMk mdifferentiableAt_const)
    exact hH.comp (1 - diskTimeProfile r) hi
  have hrad : g.tangentNorm (F (r • angularPoint t))
      (mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (angularPoint t)) ≤
        P * (g.edist center (gamma t)).toReal := by
    dsimp only [F]
    erw [m64LocalConeDiskMap_radial_column H center gamma hperiod hr t hF hslice,
      m64LocalConeDiskMap_polar H center gamma hperiod hr t]
    change ‖-deriv diskTimeProfile r • mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s => H (s, center, gamma t)) (1 - diskTimeProfile r) 1‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    change |deriv diskTimeProfile r| * g.tangentNorm _ _ ≤ _
    rw [hspeed]
    exact mul_le_mul_of_nonneg_right hprofile ENNReal.toReal_nonneg
  have hang : r * g.tangentNorm (F (r • angularPoint t))
      (mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (angularVector t)) ≤
        B * g.tangentNorm (gamma t) (curveVelocity gamma t) := by
    have hi : g.tangentNorm (F (r • angularPoint t))
        (mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (r • angularVector t)) ≤
          B * g.tangentNorm (gamma t) (curveVelocity gamma t) := by
      dsimp only [F]
      erw [m64LocalConeDiskMap_angular_column H center gamma hperiod hr t hgamma hF hH,
        m64LocalConeDiskMap_polar H center gamma hperiod hr t]
      exact hlast (curveVelocity gamma t)
    change ‖mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (r • angularVector t)‖ ≤ _ at hi
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hi
    exact hi
  have ha : 0 ≤ g.tangentNorm (F (r • angularPoint t))
      (mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (angularPoint t)) := Real.sqrt_nonneg _
  have hb : 0 ≤ g.tangentNorm (F (r • angularPoint t))
      (mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (angularVector t)) := Real.sqrt_nonneg _
  have hangular : g.tangentNorm (F (r • angularPoint t))
      (mfderiv (𝓡 2) (𝓡 n) F (r • angularPoint t) (angularVector t)) ≤
        2 * B * g.tangentNorm (gamma t) (curveVelocity gamma t) := by nlinarith
  have ha2 := mul_self_le_mul_self ha hrad
  have hb2 := mul_self_le_mul_self hb hangular
  have henergy := m64EnergyDensity_polar_frame g F (r • angularPoint t) t
  have he0 : 0 ≤ m60EnergyDensity g F (r • angularPoint t) := by rw [henergy]; positivity
  have he : m60EnergyDensity g F (r • angularPoint t) ≤
      P ^ 2 / 2 * (g.edist center (gamma t)).toReal ^ 2 +
        2 * B ^ 2 * (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
    nlinarith [ha2, hb2]
  exact (show r * m60EnergyDensity g F (r • angularPoint t) ≤
      m60EnergyDensity g F (r • angularPoint t) by nlinarith).trans he

end PoincareConjecture
