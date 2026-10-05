import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Extension.ClosedStateExtension
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Paths.ClosedPathSubstitution
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Paths.ContinuousPathFamily

/-!
# Smoothly currying a family on its actual compact time set

The parameter smoothness used for Morgan-Tian Lemma 6.22,
pp. 115-116. Localizing only the open parameter variable permits
the existing closed-time substitution theorem to apply to constant
parameter paths. The actual compact time set is retained throughout.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

universe u

namespace PoincareMT.M14

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {C : Set ℝ} [CompactSpace C] {U : Set E}

/-- A path family representing a smooth closed-time scalar or vector
family is smooth in the open parameter set, with no condition on its
off-parameter values, the path-space form of Lemma 6.22, pp. 115-116. -/
theorem contDiffOn_closedPathFamily (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    (Φ : E → C(C, F)) (hΦ : ∀ x ∈ U, ∀ t : C, Φ x t = f (t.val, x)) :
    ContDiffOn ℝ ∞ Φ U := by
  intro x hx
  obtain ⟨r, hr, g, _, hg, hgf⟩ := exists_closedTime_state_extension hU f hf hx
  let L : E →L[ℝ] C(C, E) := ContinuousLinearMap.const ℝ C
  let Ψ : E → C(C, F) := fun y => closedTimePostcomp g hg.continuousOn (L y)
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (closedTimePostcomp_contDiff hC g hg).comp L.contDiff
  have heq : Φ =ᶠ[𝓝 x] Ψ := by
    filter_upwards [ball_mem_nhds x hr, hU.mem_nhds hx] with y hy hyU
    apply ContinuousMap.ext
    intro t
    exact (hΦ y hyU t).trans (hgf ⟨t.property, ball_subset_closedBall hy⟩).symm
  exact (hΨ.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

/-- A smooth family on a compact actual time set has a smooth
continuous-path representative on its open parameter set. This
supplies the bounded-integral input to Lemma 6.22, pp. 115-116. -/
theorem exists_contDiffOn_closedPathFamily (hC : UniqueDiffOn ℝ C) (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) :
    ∃ Φ : E → C(C, F), ContDiffOn ℝ ∞ Φ U ∧
      ∀ x ∈ U, ∀ t : C, Φ x t = f (t.val, x) := by
  have hc : ContinuousOn (fun z : E × C => f (z.2.val, z.1)) (U ×ˢ univ) :=
    hf.continuousOn.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst).continuousOn
      (fun z hz => ⟨z.2.property, hz.1⟩)
  obtain ⟨Φ, _, hΦ⟩ := exists_continuousOn_pathFamily
    (fun z : E × C => f (z.2.val, z.1)) hc (0 : C(C, F))
  exact ⟨Φ, contDiffOn_closedPathFamily hC hU f hf Φ hΦ, hΦ⟩

end PoincareMT.M14
