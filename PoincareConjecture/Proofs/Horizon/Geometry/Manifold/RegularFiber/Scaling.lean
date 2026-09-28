import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
namespace Poincare.Geometry.Manifold.RegularFiber

theorem surjective_mfderiv_const_smul
    {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {f : M → Fin k → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) f x)
    (hreg : Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) f x))
    {a : ℝ} (ha : a ≠ 0) :
    Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) (fun y => a • f y) x) := by
  change Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) (a • f) x)
  rw [const_smul_mfderiv hf a]
  intro z
  obtain ⟨v,hv⟩ := hreg (a⁻¹ • z)
  refine ⟨v, ?_⟩
  change a • mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) f x v = z
  rw [hv]
  change a • (a⁻¹ • (z : Fin k → ℝ)) = z
  rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
end Poincare.Geometry.Manifold.RegularFiber
