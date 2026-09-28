import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Order.ProjIcc










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_bounded_family_height
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    {a b w : ℝ} (hab : a ≤ b)
    (h : Icc a b × sphere (0 : E) 1 → ℝ) (hh : Continuous h)
    (hbound : ∀ x, |h x| < w) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ × sphere (0 : E) 1 → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, |g x| < w) ∧
      ∀ z : Icc a b, ∀ q : sphere (0 : E) 1, |g (z, q) - h (z, q)| < ε := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = 2)]
    norm_num)
  let H : ℝ × sphere (0 : E) 1 → ℝ := fun x => h (projIcc a b hab x.1, x.2)
  have hH : Continuous H := hh.comp
    ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)
  have hHb : ∀ x, |H x| < w := fun x => hbound (projIcc a b hab x.1, x.2)
  let r : ℝ × sphere (0 : E) 1 → ℝ := fun x => min ε ((w - |H x|) / 2)
  have hr : Continuous r := continuous_const.min
    ((continuous_const.sub hH.abs).div_const 2)
  have hr0 : ∀ x, 0 < r x := by
    intro x
    exact lt_min hε (div_pos (sub_pos.mpr (hHb x)) (by norm_num))
  obtain ⟨g, hg, _⟩ := hH.exists_contMDiff_approx
    (𝓘(ℝ, ℝ).prod (𝓡 1)) (⊤ : ℕ∞) hr hr0
  have herr : ∀ x, |g x - H x| < r x := by
    intro x
    simpa only [Real.dist_eq] using hg x
  refine ⟨g, g.contMDiff, ?_, ?_⟩
  · intro x
    have hsmall := (herr x).trans_le (min_le_right ε ((w - |H x|) / 2))
    have htriangle : |g x| ≤ |g x - H x| + |H x| := by
      simpa only [Real.norm_eq_abs, sub_add_cancel] using norm_add_le (g x - H x) (H x)
    linarith [hHb x]
  · intro z q
    have hsmall := (herr ((z : ℝ), q)).trans_le
      (min_le_left ε ((w - |H ((z : ℝ), q)|) / 2))
    simpa only [H, projIcc_val] using hsmall

end PoincareConjecture.M25.Topology3D
