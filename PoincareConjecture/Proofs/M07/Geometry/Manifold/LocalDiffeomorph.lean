import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H]
  {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {r : ℕ∞ω}

theorem IsLocalDiffeomorphAt.congr_of_eventuallyEq
    {f g : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J r f x)
    (hgf : g =ᶠ[𝓝 x] f) : IsLocalDiffeomorphAt I J r g x := by
  obtain ⟨e, hx, he⟩ := hf
  obtain ⟨U, hUeq, hU, hxU⟩ := mem_nhds_iff.mp hgf
  let e' := e.toOpenPartialHomeomorph.restrOpen U hU
  let d : PartialDiffeomorph I J M N r :=
    { toPartialEquiv := e'.toPartialEquiv
      open_source := e'.open_source
      open_target := e'.open_target
      contMDiffOn_toFun := e.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := e.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨d, ⟨hx, hxU⟩, ?_⟩
  intro y hy
  exact (hUeq hy.2).trans (he hy.1)

theorem IsLocalDiffeomorphAt.of_comp
    {q : M → N} {f : N → P} {x : M}
    (hq : IsLocalDiffeomorphAt I J r q x)
    (hf : IsLocalDiffeomorphAt I K r (f ∘ q) x) :
    IsLocalDiffeomorphAt J K r f (q x) := by
  have hf' : IsLocalDiffeomorphAt I K r (f ∘ q) (hq.localInverse (q x)) := by
    rw [hq.localInverse_left_inv hq.localInverse_mem_target]
    exact hf
  apply (hq.localInverse_isLocalDiffeomorphAt.comp K P hf').congr_of_eventuallyEq
  filter_upwards [hq.localInverse_eventuallyEq_right] with y hy
  exact congrArg f hy.symm

end

namespace Poincare

theorem isLocalDiffeomorph_subtypeVal
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (U : Set H) (hU : IsOpen U)
    [Nonempty U] (r : ℕ∞ω) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph I I r (Subtype.val : U → H) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let e := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let d : PartialDiffeomorph I I U H r :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := (contMDiff_isOpenEmbedding
        (I := I) (n := r) hU.isOpenEmbedding_subtypeVal).contMDiffOn
      contMDiffOn_invFun := by
        simpa [e] using contMDiffOn_isOpenEmbedding_symm
          (I := I) (n := r) hU.isOpenEmbedding_subtypeVal }
  intro x
  exact ⟨d, mem_univ x, fun _ _ => rfl⟩

end Poincare
