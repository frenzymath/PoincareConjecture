import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Instances.Real



set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold



theorem exists_contMDiff_eq_near
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {x : M} (hx : x ∈ U) :
    ∃ F : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] f := by
  obtain ⟨χ, _, hχU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hU.mem_nhds hx)
  refine ⟨fun y => χ y * f y, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ U
    · exact χ.contMDiffAt.smul (hf.contMDiffAt (hU.mem_nhds hy))
    · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hχU h))
      filter_upwards [hz] with z hz
      simp [hz]
  · filter_upwards [χ.eventuallyEq_one] with y hy
    simp [hy]

end Poincare.Manifold
