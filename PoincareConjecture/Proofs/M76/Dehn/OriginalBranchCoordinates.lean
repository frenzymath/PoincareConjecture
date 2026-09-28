import PoincareConjecture.Proofs.M76.Dehn.OriginalPLSuccessor
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProjectedEmbedding
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse

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

theorem Step.projectionInclusion_local (step : Step s t) :
    IsLocalHomeomorph (step.projection ∘ step.inclusion) :=
  step.covering.isLocalHomeomorph.comp step.openEmbedding.isLocalHomeomorph

theorem Step.projectionInclusion_fiber (step : Step s t) (y : s.Carrier) :
    ((step.projection ∘ step.inclusion) ⁻¹' {y}).Finite ∧
      ((step.projection ∘ step.inclusion) ⁻¹' {y}).ncard ≤ 2 := by
  have hf : (step.projection ⁻¹' {y}).Finite :=
    finite_of_ncard_pos (by rw [step.two y]; norm_num)
  have h := step.openEmbedding.injective.finite_fiber_comp_ncard_le hf
  exact ⟨h.1, h.2.trans_eq (step.two y)⟩

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

theorem Step.region_preimage (step : Step s t) (R : Set M) :
    t.projection ⁻¹' R =
      (step.projection ∘ step.inclusion) ⁻¹' (s.projection ⁻¹' R) := by
  ext x
  change t.projection x ∈ R ↔ s.projection (step.projection (step.inclusion x)) ∈ R
  rw [step.original_eq]

theorem Step.frontier_preimage (step : Step s t) (R : Set M) :
    frontier (t.projection ⁻¹' R) =
      (step.projection ∘ step.inclusion) ⁻¹' frontier (s.projection ⁻¹' R) := by
  rw [t.frontier_region, s.frontier_region]
  exact step.region_preimage (frontier R)

end Geometry.OriginalPLTower
