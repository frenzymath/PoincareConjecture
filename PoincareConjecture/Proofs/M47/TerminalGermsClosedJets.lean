import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M47

theorem terminalGerms_closed_taylor_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (hconvex : Convex ℝ U)
    (f : E → F) (P : E → FormalMultilinearSeries ℝ E F)
    (hzero : ∀ x ∈ closure U, (P x 0).curry0 = f x)
    (hcontinuous : ∀ m : ℕ, ContinuousOn (fun x => P x m) (closure U))
    (hderiv : ∀ m : ℕ, ∀ x ∈ U,
      HasFDerivAt (fun y => P y m) (P x (m + 1)).curryLeft x) :
    HasFTaylorSeriesUpToOn ∞ f P (closure U) ∧ ContDiffOn ℝ ∞ f (closure U) := by
  have hwithin (m : ℕ) (x : E) (hx : x ∈ closure U) :
      HasFDerivWithinAt (fun y => P y m) (P x (m + 1)).curryLeft (closure U) x := by
    have hlimit : Tendsto (fun y => fderiv ℝ (fun z => P z m) y)
        (𝓝[U] x) (𝓝 (P x (m + 1)).curryLeft) := by
      have hc := ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) F).continuous.tendsto (P x (m + 1))).comp
          ((hcontinuous (m + 1) x hx).mono subset_closure)
      apply hc.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hderiv m y hy).fderiv.symm
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hderiv m y hy).differentiableAt.differentiableWithinAt)
      hconvex hU (fun y hy => (hcontinuous m y hy).mono subset_closure) hlimit
  have hseries : HasFTaylorSeriesUpToOn ∞ f P (closure U) :=
    ⟨hzero, fun m _ x hx => hwithin m x hx, fun m _ => hcontinuous m⟩
  exact ⟨hseries, hseries.contDiffOn⟩

end PoincareConjecture.M47
