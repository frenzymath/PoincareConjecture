import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.Spacetime.Realization.Box.Spatial.Calculus
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Actual charts of open Euclidean subsets

The spatial coordinate argument in Morgan-Tian Definition 3.38 and
Lemma 6.4, pp. 61, 107-108, retains the given open-subset chart.
Its source, target, values and inverse differential are identified here.
-/

set_option autoImplicit false
-- The chart and inverse-chart tangent fibers use the ambient vector model.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] (U : Opens E)

/-- Every selected chart of an open Euclidean subset is its actual
inclusion, the spatial coordinates in Definition 3.38, p. 61. -/
theorem chartAt_apply_eq_val (x y : U) : chartAt E x y = y.val := rfl

/-- An open Euclidean subset's selected charts have the whole subtype
as source, Definition 3.38 and Lemma 6.4, pp. 61, 107-108. -/
theorem chartAt_source_eq_univ (x : U) : (chartAt E x).source = univ := by
  simp only [chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source,
    OpenPartialHomeomorph.refl_source, preimage_univ]

/-- The selected chart inverse recovers each actual included spatial
point, Definition 3.38 and Lemma 6.4, pp. 61, 107-108. -/
theorem chartAt_symm_apply_val (x y : U) : (chartAt E x).symm y.val = y := by
  rw [← U.chartAt_apply_eq_val x y]
  exact (chartAt E x).left_inv (by rw [U.chartAt_source_eq_univ]; exact mem_univ y)

/-- The chart target is exactly the original open spatial subset,
Definition 3.38 and Lemma 6.4, pp. 61, 107-108. -/
theorem chartAt_target_eq (x : U) : (chartAt E x).target = (U : Set E) := by
  ext z
  constructor
  · intro hz
    have hval := (chartAt E x).right_inv hz
    rw [U.chartAt_apply_eq_val] at hval
    exact hval ▸ ((chartAt E x).symm z).property
  · intro hz
    have hmem : (⟨z, hz⟩ : U) ∈ (chartAt E x).source := by
      rw [U.chartAt_source_eq_univ]
      exact mem_univ _
    exact (chartAt E x).map_source hmem

variable [NormedSpace ℝ E]

/-- The inverse chart has the actual identity differential on its
spatial target, so it does not alter the metric coefficients in the
coordinate calculation of Lemma 6.4, pp. 107-108. -/
theorem mfderiv_chartAt_symm_val (x y : U) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (chartAt E x).symm y.val = ContinuousLinearMap.id ℝ E := by
  have hy : y.val ∈ (chartAt E x).target := by
    rw [U.chartAt_target_eq]
    exact y.property
  have hs : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (chartAt E x).symm y.val :=
    ((contMDiffOn_chart_symm (n := ∞) y.val hy).contMDiffAt
      ((chartAt E x).open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (Subtype.val : U → E)
      ((chartAt E x).symm y.val) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have heq : (Subtype.val ∘ (chartAt E x).symm) =ᶠ[𝓝 y.val] (id : E → E) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds hy] with z hz
    exact (chartAt E x).right_inv hz
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
  rw [mfderiv_comp y.val hi hs, PoincareMT.Proofs.M11.mfderiv_openSubtype_val,
    mfderiv_id] at hd
  exact hd

end TopologicalSpace.Opens
