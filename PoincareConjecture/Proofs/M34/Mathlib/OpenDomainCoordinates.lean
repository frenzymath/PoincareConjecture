import PoincareConjecture.Proofs.M34.Mathlib.OpenInclusionDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

section Topological

variable {E : Type*} [TopologicalSpace E] {U : Set E} (hU : IsOpen U) [Nonempty U]

theorem canonicalOpen_chart_eq :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p q : U, chartAt E p = chartAt E q := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p q
  rfl

theorem canonicalOpen_chart_source :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p : U, (chartAt E p).source = univ := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p
  exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_source _

theorem canonicalOpen_chart_target :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p : U, (chartAt E p).target = U := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p
  change (hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : U → E)).target = U
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]

theorem canonicalOpen_chart_symm_apply :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p q : U, (chartAt E p).symm (q : E) = q := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p q
  exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv _

theorem canonicalOpen_chart_coe_symm :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ (p : U) (x : E), x ∈ U → ((chartAt E p).symm x : E) = x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p x hx
  exact congrArg Subtype.val (canonicalOpen_chart_symm_apply hU p ⟨x, hx⟩)

end Topological

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {U : Set E} (hU : IsOpen U) [Nonempty U]

theorem canonicalOpen_extChart_target :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p : U, (extChartAt 𝓘(𝕜, E) p).target = U := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p
  rw [extChartAt_target, canonicalOpen_chart_target hU]
  simp

theorem canonicalOpen_mfderiv_symm :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
    ∀ (p : U) (x : E), x ∈ U →
      mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) (extChartAt 𝓘(𝕜, E) p).symm x =
        ContinuousLinearMap.id 𝕜 E := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  intro p x hx
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(𝕜, E)) (x := (⟨x, hx⟩ : U))
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  exact hd

theorem canonicalOpen_contMDiffAt_symm :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
    ∀ (p : U) (x : E), x ∈ U →
      ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ∞ (extChartAt 𝓘(𝕜, E) p).symm x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  intro p x hx
  have hh := contMDiffOn_extChartAt_symm (I := 𝓘(𝕜, E)) (n := ∞) p
  rw [canonicalOpen_extChart_target hU] at hh
  exact (hh x hx).contMDiffAt (hU.mem_nhds hx)

theorem canonicalOpen_mfderiv_restrict
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H] [TopologicalSpace N]
    (I : ModelWithCorners 𝕜 F H) [ChartedSpace H N]
    {e : E → N} {x : U} (he : MDifferentiableAt 𝓘(𝕜, E) I e (x : E)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    mfderiv 𝓘(𝕜, E) I (fun y : U => e y) x = mfderiv 𝓘(𝕜, E) I e (x : E) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓘(𝕜, E)) (n := ∞)
  have hc : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) (Subtype.val : U → E) x :=
    (contMDiff_isOpenEmbedding (I := 𝓘(𝕜, E)) (n := ∞)
      hU.isOpenEmbedding_subtypeVal).mdifferentiable (by simp) x
  have hh := mfderiv_comp x he hc
  rw [mfderiv_subtypeVal_singleton hU] at hh
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun A => A v) hh
