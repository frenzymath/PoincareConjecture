import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M58

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N]

theorem continuousAt_tangentMap_of_contMDiffAt {f : M → N}
    {v : TangentBundle I M} (hf : ContMDiffAt I J 1 f v.proj) :
    ContinuousAt (tangentMap I J f) v := by
  let s : Set M := {x | ContMDiffAt I J 1 f x}
  have hs : IsOpen s := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hx
  have hfs : ContMDiffOn I J 1 f s := fun _ hx => hx.contMDiffWithinAt
  have hv : v ∈ (π E (TangentSpace I) ⁻¹' s) := hf
  have hopen : IsOpen (π E (TangentSpace I) ⁻¹' s) :=
    hs.preimage (FiberBundle.continuous_proj E (TangentSpace I))
  have hcont := (hfs.continuousOn_tangentMapWithin le_rfl hs.uniqueMDiffOn) v hv
  apply (hcont.continuousAt (hopen.mem_nhds hv)).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hv] with w hw
  exact (tangentMapWithin_eq_tangentMap (hs.uniqueMDiffOn _ hw)
    (hw.mdifferentiableAt one_ne_zero)).symm

end PoincareConjecture.Proofs.M58
