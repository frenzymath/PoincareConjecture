import Mathlib.Geometry.Manifold.Instances.Sphere











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
variable {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]



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

end PoincareConjecture.M25.Topology3D
