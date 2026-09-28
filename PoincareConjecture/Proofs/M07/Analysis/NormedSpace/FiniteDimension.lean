import Mathlib.Analysis.Normed.Module.FiniteDimension



set_option autoImplicit false
open Filter
open scoped Topology

namespace Poincare.Analysis



theorem tendsto_continuousLinearMap_of_basis
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {g : E →L[ℝ] F}
    (h : ∀ i, Tendsto (fun a => f a (b i)) l (𝓝 (g (b i)))) :
    Tendsto f l (𝓝 g) := by
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  let ev : (E →L[ℝ] F) →ₗ[ℝ] (ι → F) :=
    { toFun := fun A i => A (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro A B hAB
    apply ContinuousLinearMap.coe_injective
    exact b.ext (fun i => congrFun hAB i)
  have he := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  apply he.isInducing.tendsto_nhds_iff.mpr
  exact tendsto_pi_nhds.mpr h

end Poincare.Analysis
