import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.Flat
open MeasureTheory Set
open scoped ContDiff

namespace Poincare.Analysis


theorem scalarCriticalImage_null_flat_residual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {V : Set E} (hV : IsOpen V)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f V) {n : ℕ}
    (hn : Module.finrank ℝ E < n + 1) :
    volume (f '' {x | x ∈ V ∧ ∀ k, 1 ≤ k → k ≤ n →
      iteratedFDeriv ℝ k f x = 0}) = 0 := by
  exact scalar_flat_image_null hV hf (fun x hx => hx.1)
    (Nat.lt_succ_iff.mp hn) (fun x hx => hx.2)

end Poincare.Analysis
