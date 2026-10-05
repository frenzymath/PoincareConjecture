import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth sphere-valued maps on open domains

The existing smooth structure on the sphere detects smoothness through
its ambient inclusion on an open domain. Restriction to an open source
submanifold reduces this to Mathlib's sphere codomain restriction theorem.
This supports radial collar coordinates in the collar form of Hatcher,
Notes on Basic 3-Manifold Topology, Theorem 1.1, pp. 1-3.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
variable {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Ambient smoothness of a sphere-valued map on an open domain gives
smoothness for the existing sphere manifold structure. -/
theorem contMDiffOn_sphere_of_coe {U : Set M} (hU : IsOpen U)
    (f : M → sphere (0 : E) 1)
    (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ (fun x => (f x : E)) U) :
    ContMDiffOn I (𝓡 n) ∞ f U := by
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  have hcoe : ContMDiff I 𝓘(ℝ, E) ∞ (fun x : V => (f x : E)) := by
    intro x
    exact contMDiffAt_subtype_iff.mpr (hf.contMDiffAt (hU.mem_nhds x.2))
  have hV : ContMDiff I (𝓡 n) ∞ (fun x : V => f x) :=
    hcoe.codRestrict_sphere (fun x => (f x).2)
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (hV (⟨x, hx⟩ : V))).contMDiffWithinAt

end PoincareMT.M25.Topology3D
