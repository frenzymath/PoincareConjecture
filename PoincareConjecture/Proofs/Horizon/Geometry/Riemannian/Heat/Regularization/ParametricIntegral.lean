import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Poincare.Analysis.Heat

variable {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace A] {μ : Measure A} {U : Set E} {f : E → A → F}

theorem contDiffOn_integral_of_locally_dominated_iteratedFDeriv
    (hU : IsOpen U)
    (hf : ∀ᵐ a ∂μ, ContDiffOn ℝ ∞ (fun x => f x a) U)
    (hmeas : ∀ (m : ℕ) (x : E), x ∈ U →
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ m (fun z => f z a) x) μ)
    (hbound : ∀ (x : E), x ∈ U → ∀ m : ℕ,
      ∃ V ∈ 𝓝 x, ∃ bound : A → ℝ, Integrable bound μ ∧
        ∀ᵐ a ∂μ, ∀ z ∈ V, ‖iteratedFDeriv ℝ m (fun w => f w a) z‖ ≤ bound a) :
    ContDiffOn ℝ ∞ (fun x => ∫ a, f x a ∂μ) U ∧
      ∀ (m : ℕ) (x : E), x ∈ U →
        iteratedFDeriv ℝ m (fun z => ∫ a, f z a ∂μ) x =
          ∫ a, iteratedFDeriv ℝ m (fun z => f z a) x ∂μ := by
  let p : E → FormalMultilinearSeries ℝ E F :=
    fun x m => ∫ a, iteratedFDeriv ℝ m (fun z => f z a) x ∂μ
  have hi (m : ℕ) (x : E) (hx : x ∈ U) :
      Integrable (fun a => iteratedFDeriv ℝ m (fun z => f z a) x) μ := by
    obtain ⟨V, hV, bound, hb, hdom⟩ := hbound x hx m
    apply hb.mono' (hmeas m x hx)
    filter_upwards [hdom] with a ha
    exact ha x (mem_of_mem_nhds hV)
  have hd (m : ℕ) (x : E) (hx : x ∈ U) :
      HasFDerivAt (fun z => p z m) (p x (m + 1)).curryLeft x := by
    let L : (E [×(m + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [×m]→L[ℝ] F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
    obtain ⟨V, hV, bound, hb, hdom⟩ := hbound x hx (m + 1)
    have hdmeas : AEStronglyMeasurable
        (fun a => fderiv ℝ (iteratedFDeriv ℝ m (fun z => f z a)) x) μ := by
      simpa [L, fderiv_iteratedFDeriv, Function.comp_def] using
        L.continuous.comp_aestronglyMeasurable (hmeas (m + 1) x hx)
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun z a => iteratedFDeriv ℝ m (fun w => f w a) z)
      (F' := fun z a => fderiv ℝ (iteratedFDeriv ℝ m (fun w => f w a)) z)
      (s := V ∩ U) (bound := bound) (inter_mem hV (hU.mem_nhds hx))
      (Filter.eventually_of_mem (hU.mem_nhds hx) (fun z hz => hmeas m z hz))
      (hi m x hx) hdmeas
      (by
        filter_upwards [hdom] with a ha
        intro z hz
        rw [norm_fderiv_iteratedFDeriv]
        exact ha z hz.1)
      hb
      (by
        filter_upwards [hf] with a ha
        intro z hz
        exact ((ha.contDiffAt (hU.mem_nhds hz.2)).differentiableAt_iteratedFDeriv (m := m)
          (by exact_mod_cast (WithTop.coe_lt_top m : (m : ℕ∞) < ⊤))).hasFDerivAt)
    change HasFDerivAt (fun z => p z m)
      (∫ a, L (iteratedFDeriv ℝ (m + 1) (fun z => f z a) x) ∂μ) x at h
    have heq := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
      (E := E [×(m + 1)]→L[ℝ] F) (Fₗ := E →L[ℝ] E [×m]→L[ℝ] F)
      L (hi (m + 1) x hx)
    rw [heq] at h
    exact h
  have hp : HasFTaylorSeriesUpToOn ∞ (fun x => ∫ a, f x a ∂μ) p U := by
    constructor
    · intro x hx
      change (continuousMultilinearCurryFin0 ℝ E F)
        (∫ a, iteratedFDeriv ℝ 0 (fun z => f z a) x ∂μ) = _
      exact ((continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.integral_comp_comm
        (fun a => iteratedFDeriv ℝ 0 (fun z => f z a) x)).symm
    · intro m _ x hx
      exact (hd m x hx).hasFDerivWithinAt
    · intro m _ x hx
      exact (hd m x hx).continuousAt.continuousWithinAt
  refine ⟨hp.contDiffOn, ?_⟩
  intro m x hx
  have hm : (m : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    ((hp.contDiffOn.contDiffAt (hU.mem_nhds hx)).of_le hm) hx]
  exact (hp.eq_iteratedFDerivWithin_of_uniqueDiffOn hm hU.uniqueDiffOn hx).symm

end Poincare.Analysis.Heat
