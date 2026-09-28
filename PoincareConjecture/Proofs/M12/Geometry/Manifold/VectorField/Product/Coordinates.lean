import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold.VectorField

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]

theorem mfderiv_extChartAt_prod_snd_eventuallyEq
    (Z : (q : M × N) → TangentSpace (I.prod J) q) (p : M × N) :
    (fun q => (mfderiv (I.prod J) 𝓘(ℝ, E × E')
      (extChartAt (I.prod J) p) q (Z q)).2) =ᶠ[𝓝 p]
      (fun q => mfderiv J 𝓘(ℝ, E') (extChartAt J p.2) q.2 (Z q).2) := by
  have hfst : ∀ᶠ q : M × N in 𝓝 p, q.1 ∈ (extChartAt I p.1).source :=
    continuous_fst.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) p.1).mem_nhds (mem_extChartAt_source p.1))
  have hsnd : ∀ᶠ q : M × N in 𝓝 p, q.2 ∈ (extChartAt J p.2).source :=
    continuous_snd.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := J) p.2).mem_nhds (mem_extChartAt_source p.2))
  filter_upwards [hfst, hsnd] with q hq₁ hq₂
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p.1) q.1 :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hq₁)
  have hg : MDifferentiableAt J 𝓘(ℝ, E') (extChartAt J p.2) q.2 :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hq₂)
  have hd : (show E × E' →L[ℝ] E × E' from
      mfderiv (I.prod J) 𝓘(ℝ, E × E') (extChartAt (I.prod J) p) q) =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p.1) q.1).prodMap
        (mfderiv J 𝓘(ℝ, E') (extChartAt J p.2) q.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      extChartAt_prod, PartialEquiv.prod_coe]
    exact mfderiv_prodMap hf hg
  exact congrArg (fun L : E × E' →L[ℝ] E × E' => (L (Z q)).2) hd

end Poincare.Manifold.VectorField
