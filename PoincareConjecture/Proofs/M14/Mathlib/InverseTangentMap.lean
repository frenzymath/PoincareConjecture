import Mathlib.Geometry.Manifold.VectorField.Pullback










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

variable {𝕜 E H M E' H' N EP HP P : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  [TopologicalSpace HP] {L : ModelWithCorners 𝕜 EP HP}
  [TopologicalSpace P] [ChartedSpace HP P]
  {m n : ℕ∞ω} {f : M → N} {x : M}




theorem ContMDiffAt.inverse_mfderiv_const
    (hf : ContMDiffAt I J n f x) (hinv : (mfderiv I J f x).IsInvertible)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(𝕜, E' →L[𝕜] E) m
      (fun y => inCoordinates E' (TangentSpace J : N → Type _) E
        (TangentSpace I : M → Type _) (f x) (f y) x y (mfderiv I J f y).inverse) x := by
  have hd : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E') m
      (fun y => inCoordinates E (TangentSpace I : M → Type _) E'
        (TangentSpace J : N → Type _) x y (f x) (f y) (mfderiv I J f y)) x :=
    hf.mfderiv_const hmn
  have hi : ContMDiffAt I 𝓘(𝕜, E' →L[𝕜] E) m
      (ContinuousLinearMap.inverse ∘ (fun y => inCoordinates E
        (TangentSpace I : M → Type _) E' (TangentSpace J : N → Type _)
        x y (f x) (f y) (mfderiv I J f y))) x := by
    apply ContMDiffAt.comp x _ hd
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x)
      (FiberBundle.mem_baseSet_trivializationAt' (f x))]
    exact isInvertible_equiv.comp (hinv.comp isInvertible_equiv)
  apply hi.congr_of_eventuallyEq
  have hsrc := (trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)
  have htgt := hf.continuousAt.preimage_mem_nhds
    ((trivializationAt E' (TangentSpace J : N → Type _) (f x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (f x)))
  filter_upwards [hsrc, htgt] with y hy hfy
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hfy hy, inCoordinates_eq hy hfy]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm]
  rfl




theorem ContMDiffWithinAt.inverse_mfderiv_apply
    {b : P → M} {Y : ∀ z, TangentSpace J (f (b z))} {S : Set P} {z : P}
    (hY : ContMDiffWithinAt L J.tangent m
      (fun w => TotalSpace.mk' E' (f (b w)) (Y w)) S z)
    (hb : ContMDiffWithinAt L I m b S z) (hf : ContMDiffAt I J n f (b z))
    (hinv : (mfderiv I J f (b z)).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt L I.tangent m
      (fun w => TotalSpace.mk' E (b w) ((mfderiv I J f (b w)).inverse (Y w))) S z := by
  have hi := (hf.inverse_mfderiv_const hinv hmn).comp_contMDiffWithinAt z hb
  exact hi.clm_apply_of_inCoordinates hY hb
