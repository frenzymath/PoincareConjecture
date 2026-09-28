import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting










open Set Filter
open scoped ContDiff Topology

namespace Poincare.Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem contDiff_of_exp_comp {n : WithTop ℕ∞} {f L : E → ℂ}
    (hf : ContDiff ℝ n f) (hL : Continuous L)
    (hlift : ∀ x, Complex.exp (L x) = f x) : ContDiff ℝ n L := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hlog : ContDiffAt ℝ n
      (fun y => Complex.log (f y / f x) + L x) x := by
    have hfx : f x ≠ 0 := hlift x ▸ Complex.exp_ne_zero (L x)
    have hslit : f x / f x ∈ Complex.slitPlane := by
      simp [div_self hfx]
    have hc : ContDiffAt ℝ n Complex.log (f x / f x) :=
      (Complex.contDiffAt_log hslit).restrict_scalars ℝ
    exact (hc.comp x (hf.contDiffAt.div_const (f x))).add contDiffAt_const
  apply hlog.congr_of_eventuallyEq
  have hsmall : ∀ᶠ y in 𝓝 x,
      -Real.pi < (L y - L x).im ∧ (L y - L x).im < Real.pi := by
    have hc : Continuous (fun y => (L y - L x).im) := by fun_prop
    exact hc.continuousAt (Ioo_mem_nhds (by simpa using Real.pi_pos)
      (by simpa using Real.pi_pos))
  filter_upwards [hsmall] with y hy
  rw [← hlift y, ← hlift x, ← Complex.exp_sub,
    Complex.log_exp hy.1 hy.2.le, sub_add_cancel]



theorem exists_contDiff_logarithm {n : WithTop ℕ∞} {f : E → ℂ}
    (hf : ContDiff ℝ n f) (hne : ∀ x, f x ≠ 0)
    (x₀ : E) (z₀ : ℂ) (h₀ : Complex.exp z₀ = f x₀) :
    ∃ L : E → ℂ, ContDiff ℝ n L ∧ L x₀ = z₀ ∧
      ∀ x, Complex.exp (L x) = f x := by
  obtain ⟨L, ⟨hL₀, hL⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      ⟨f, hf.continuous⟩ h₀ (by simpa using hne)
  have hlift (x : E) : Complex.exp (L x) = f x := congrFun hL x
  exact ⟨L, contDiff_of_exp_comp hf L.continuous hlift, hL₀, hlift⟩



theorem exists_contDiff_logarithm_eq_zero {n : WithTop ℕ∞} {f : E → ℂ}
    (hf : ContDiff ℝ n f) (hne : ∀ x, f x ≠ 0)
    {U : Set E} (hU : IsPreconnected U) (hUne : U.Nonempty)
    (hfix : ∀ x ∈ U, f x = 1) :
    ∃ L : E → ℂ, ContDiff ℝ n L ∧ (∀ x, Complex.exp (L x) = f x) ∧
      ∀ x ∈ U, L x = 0 := by
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨L, hL, hL₀, hlift⟩ := exists_contDiff_logarithm hf hne x₀ 0
    (by simpa using (hfix x₀ hx₀).symm)
  refine ⟨L, hL, hlift, ?_⟩
  intro x hx
  exact Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hU
    hL.continuous.continuousOn continuousOn_const
    (fun y hy => Subtype.ext (by simpa [hlift] using hfix y hy)) hx₀ hL₀ hx

end Poincare.Complex
