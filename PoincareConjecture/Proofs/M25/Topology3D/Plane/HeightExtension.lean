import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialExtension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_ambient_height_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (q0 : sphere (0 : E) 1)
    (g : ℝ × sphere (0 : E) 1 → ℝ)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g)
    {w : ℝ} (hbound : ∀ p, |g p| < w) :
    ∃ H : ℝ × E → ℝ, ContDiff ℝ ∞ H ∧
      (∀ z : ℝ, ∀ q : sphere (0 : E) 1, H (z, (q : E)) = g (z, q)) ∧
      (∀ p, |H p| < w) ∧
      ∀ p, ‖p.2‖ ≤ 1 / 2 ∨ 2 ≤ ‖p.2‖ → H p = 0 := by
  let b : E → ℝ := fun x => Real.smoothTransition (4 * ‖x‖ ^ 2 - 1) *
    Real.smoothTransition (4 - ‖x‖ ^ 2)
  have hb : ContDiff ℝ ∞ b :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_norm_sq ℝ)).sub contDiff_const)).mul
        (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ)))
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hb1 : ∀ x, b x ≤ 1 := by
    intro x
    dsimp only [b]
    nlinarith [Real.smoothTransition.nonneg (4 * ‖x‖ ^ 2 - 1),
      Real.smoothTransition.le_one (4 * ‖x‖ ^ 2 - 1),
      Real.smoothTransition.le_one (4 - ‖x‖ ^ 2)]
  have hbzero : ∀ x, ‖x‖ ≤ 1 / 2 ∨ 2 ≤ ‖x‖ → b x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · have harg : 4 * ‖x‖ ^ 2 - 1 ≤ 0 := by nlinarith [norm_nonneg x]
      simp only [b, Real.smoothTransition.zero_of_nonpos harg, zero_mul]
    · have harg : 4 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
      simp only [b, Real.smoothTransition.zero_of_nonpos harg, mul_zero]
  have hbsphere : ∀ q : sphere (0 : E) 1, b (q : E) = 1 := by
    intro q
    simp only [b, norm_eq_of_mem_sphere q]
    norm_num [Real.smoothTransition.one_of_one_le]
  let C : ℝ × E → ℝ := radialFamilyExtension q0 (fun z q => g (z, q))
  let H : ℝ × E → ℝ := fun p => b p.2 * C p
  have hzero : ∀ p : ℝ × E, ‖p.2‖ ≤ 1 / 2 ∨ 2 ≤ ‖p.2‖ → H p = 0 := by
    intro p hp
    simp only [H, hbzero p.2 hp, zero_mul]
  have hC : ContDiffOn ℝ ∞ C (univ ×ˢ ({0} : Set E)ᶜ) :=
    contDiffOn_radialFamilyExtension q0 (fun z q => g (z, q)) hg
  have hH : ContDiff ℝ ∞ H := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.2 = 0
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hnear : ∀ᶠ y : ℝ × E in nhds p, ‖y.2‖ < (1 / 2 : ℝ) :=
        (continuous_snd.norm.continuousAt).eventually_lt continuousAt_const
          (by simp [hp])
      filter_upwards [hnear] with y hy
      exact hzero y (Or.inl hy.le)
    · exact (hb.comp contDiff_snd).contDiffAt.mul
        (hC.contDiffAt ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds
          ⟨mem_univ _, hp⟩))
  refine ⟨H, hH, ?_, ?_, hzero⟩
  · intro z q
    simp only [H, hbsphere q, one_mul, C, radialFamilyExtension_apply_sphere]
  · intro p
    have hCb : |C p| < w := hbound (p.1, unitRadialProjection q0 p.2)
    calc
      |H p| = b p.2 * |C p| := by simp only [H, abs_mul, abs_of_nonneg (hb0 p.2)]
      _ ≤ |C p| := mul_le_of_le_one_left (abs_nonneg _) (hb1 p.2)
      _ < w := hCb

end PoincareConjecture.M25.Topology3D
