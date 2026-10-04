import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalPLSuccessor
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Maps.Mathlib.ProjectedEmbedding
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffineInverse

/-!
# Original coordinates on actual tower branches

Every branch of the literal projection and open inclusion has PL
coordinates on the whole transition source. Its inverse regularity
follows from the actual PL inverse criterion. The same original
projection retains the complete region and frontier equations.
See Dehn028, section3, and Hatcher pp.45--46.
-/

set_option autoImplicit false

open Set Topology Geometry

namespace Geometry.OriginalPLTower

variable {U E M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}

/-- The actual projection composed with the actual open inclusion
is a local homeomorphism. See Dehn028, section2. -/
theorem Step.projectionInclusion_local (step : Step s t) :
    IsLocalHomeomorph (step.projection ∘ step.inclusion) :=
  step.covering.isLocalHomeomorph.comp step.openEmbedding.isLocalHomeomorph

/-- Each complete fiber of the actual step is finite of cardinality
at most two, even when the open inclusion omits one or both sheets.
See Dehn028, section2. -/
theorem Step.projectionInclusion_fiber (step : Step s t) (y : s.Carrier) :
    ((step.projection ∘ step.inclusion) ⁻¹' {y}).Finite ∧
      ((step.projection ∘ step.inclusion) ⁻¹' {y}).ncard ≤ 2 := by
  have hf : (step.projection ⁻¹' {y}).Finite :=
    finite_of_ncard_pos (by rw [step.two y]; norm_num)
  have h := step.openEmbedding.injective.finite_fiber_comp_ncard_le hf
  exact ⟨h.1, h.2.trans_eq (step.two y)⟩

/-- A branch's complete original coordinate transition is PL.
The forward formula restricts the actual lower-stage transition;
the proved inverse criterion supplies the inverse as well.
See Dehn028, section3. -/
theorem Step.branch_chart_PL (step : Step s t)
    (B : OpenPartialHomeomorph t.Carrier s.Carrier)
    (hB : EqOn B (step.projection ∘ step.inclusion) B.source)
    (k : t.Index) (l : s.Index) :
    (t.charts k).symm.trans (B.trans (s.charts l)) ∈ piecewiseAffineGroupoid E := by
  let T := (t.charts k).symm.trans (B.trans (s.charts l))
  let A := (s.charts (step.chartIndex k)).symm.trans (s.charts l)
  have heq : EqOn T A T.source := by
    intro z hz
    change s.charts l (B ((t.charts k).symm z)) =
      s.charts l ((s.charts (step.chartIndex k)).symm z)
    exact congrArg (s.charts l)
      ((hB hz.2.1).trans (step.chart_inverse k hz.1))
  have hsub : T.source ⊆ A.source := by
    intro z hz
    refine ⟨step.chart_target k hz.1, ?_⟩
    have hi : B ((t.charts k).symm z) =
        (s.charts (step.chartIndex k)).symm z :=
      (hB hz.2.1).trans (step.chart_inverse k hz.1)
    change (s.charts (step.chartIndex k)).symm z ∈ (s.charts l).source
    rw [← hi]
    exact hz.2.2
  apply (mem_piecewiseAffineGroupoid_iff_forward T).mpr
  exact (((mem_piecewiseAffineGroupoid_iff_forward A).mp
    (s.compatible (step.chartIndex k) l)).mono T.open_source hsub).congr heq.symm

/-- The same original region pulls back on every point of the
actual step, before any branch restriction. See Dehn028, section3. -/
theorem Step.region_preimage (step : Step s t) (R : Set M) :
    t.projection ⁻¹' R =
      (step.projection ∘ step.inclusion) ⁻¹' (s.projection ⁻¹' R) := by
  ext x
  change t.projection x ∈ R ↔ s.projection (step.projection (step.inclusion x)) ∈ R
  rw [step.original_eq]

/-- The complete frontier obeys the literal original projection
equation, on the whole stage and hence on both branch windows.
See Dehn028, section3. -/
theorem Step.frontier_preimage (step : Step s t) (R : Set M) :
    frontier (t.projection ⁻¹' R) =
      (step.projection ∘ step.inclusion) ⁻¹' frontier (s.projection ⁻¹' R) := by
  rw [t.frontier_region, s.frontier_region]
  exact step.region_preimage (frontier R)

end Geometry.OriginalPLTower
