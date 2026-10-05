import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.OpenInclusionDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Coordinates of the canonical open subtype

The singleton inclusion chart has exactly the given open target. Its inverse
has identity differential and is smooth at every point of that target.
The inverse's arbitrary values outside the target are never used.
These adapters serve Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

section Topological

variable {E : Type*} [TopologicalSpace E] {U : Set E} (hU : IsOpen U) [Nonempty U]

/-- The chosen inclusion chart is independent of its center
(Section 12.5, pp. 309-319). -/
theorem canonicalOpen_chart_eq :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p q : U, chartAt E p = chartAt E q := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p q
  rfl

/-- The singleton chart has the entire subtype as its source
(Section 12.5, pp. 309-319). -/
theorem canonicalOpen_chart_source :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p : U, (chartAt E p).source = univ := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p
  exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_source _

/-- The singleton chart has exactly the prescribed open set as target
(Section 12.5, pp. 309-319). -/
theorem canonicalOpen_chart_target :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p : U, (chartAt E p).target = U := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p
  change (hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : U → E)).target = U
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]

/-- The inverse chart takes a subtype value back to that exact point
(Section 12.5, pp. 309-319). -/
theorem canonicalOpen_chart_symm_apply :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p q : U, (chartAt E p).symm (q : E) = q := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p q
  exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv _

/-- On its true target the inverse chart has the original ambient value
(Section 12.5, pp. 309-319). -/
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

/-- The extended chart also has exactly the prescribed open target
(Section 12.5, pp. 309-319). -/
theorem canonicalOpen_extChart_target :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ∀ p : U, (extChartAt 𝓘(𝕜, E) p).target = U := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro p
  rw [extChartAt_target, canonicalOpen_chart_target hU]
  simp

/-- The inverse extended chart has identity differential on its true target
(Section 12.5, pp. 309-319). -/
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

/-- The actual inverse chart is smooth at every point of the open target
(Section 12.5, pp. 309-319). -/
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

/-- Restricting an ambient differentiable map preserves its differential
in the canonical inclusion coordinates (Section 12.5, pp. 309-319). -/
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
