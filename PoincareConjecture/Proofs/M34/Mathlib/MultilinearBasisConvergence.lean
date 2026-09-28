import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis

set_option autoImplicit false

open Filter
open scoped Topology

theorem ContinuousMultilinearMap.tendsto_of_basis
    {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Finite ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {κ : ι → Type*} [∀ i, Finite (κ i)] (b : ∀ i, Module.Basis (κ i) 𝕜 (E i))
    {α : Type*} {l : Filter α} {f : α → ContinuousMultilinearMap 𝕜 E F}
    {g : ContinuousMultilinearMap 𝕜 E F}
    (h : ∀ v : (i : ι) → κ i,
      Tendsto (fun a => f a (fun i => b i (v i))) l (𝓝 (g (fun i => b i (v i))))) :
    Tendsto f l (𝓝 g) := by
  let ev : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] (((i : ι) → κ i) → F) :=
    { toFun := fun A v => A (fun i => b i (v i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro A B hAB
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    exact Module.Basis.ext_multilinear b (fun v => congrFun hAB v)
  let : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 E F) :=
    FiniteDimensional.of_injective ev hinj
  have he := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  apply he.isInducing.tendsto_nhds_iff.mpr
  exact tendsto_pi_nhds.mpr h
