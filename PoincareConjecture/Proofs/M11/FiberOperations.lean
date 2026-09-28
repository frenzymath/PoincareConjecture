import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ p, TopologicalSpace (E p)]
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {b : M → B} {s t : ∀ x : M, E (b x)}

theorem contMDiff_fiber_sub
    (hs : ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F (b x) (s x)))
    (ht : ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F (b x) (t x))) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F (b x) (s x - t x)) := by
  intro x
  have hsx := contMDiffAt_totalSpace.mp (hs x)
  have htx := contMDiffAt_totalSpace.mp (ht x)
  apply contMDiffAt_totalSpace.mpr
  refine ⟨hsx.1, ?_⟩
  let e := trivializationAt F E (b x)
  apply (hsx.2.sub htx.2).congr_of_eventuallyEq
  filter_upwards [hsx.1.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F E (b x)))] with y hy
  exact (e.linear ℝ hy).map_sub (s y) (t y)

theorem contMDiff_fiber_smul {f : M → ℝ}
    (hf : ContMDiff IM 𝓘(ℝ) ∞ f)
    (hs : ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F (b x) (s x))) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F (b x) (f x • s x)) := by
  intro x
  have hsx := contMDiffAt_totalSpace.mp (hs x)
  apply contMDiffAt_totalSpace.mpr
  refine ⟨hsx.1, ?_⟩
  let e := trivializationAt F E (b x)
  apply ((hf x).smul hsx.2).congr_of_eventuallyEq
  filter_upwards [hsx.1.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F E (b x)))] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (s y)

end PoincareConjecture.Proofs.M11
