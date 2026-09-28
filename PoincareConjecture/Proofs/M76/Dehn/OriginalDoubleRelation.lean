import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteDoubleRelation
import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates
import PoincareConjecture.Proofs.M76.Wall.CutDiskProjection

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_finite_projected_double_complex
    {s t : Stage e S f r C} (step : Step s t)
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space => j x)) :
    ∃ L : SimplicialComplex ℝ (V2 × V2), L.faces.Finite ∧
      L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
        step.projection (step.inclusion (j z.1)) =
          step.projection (step.inclusion (j z.2)) ∧ z.1 ≠ z.2} := by
  let p : V2 → s.Carrier := (step.projection ∘ step.inclusion) ∘ j
  have hp : PolyhedralPLInCharts s.charts p K.space :=
    hj.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ => congrFun (step.chart_forward k) x)
  have hlocal : IsLocallyInjective (fun x : K.space => p x) :=
    step.projectionInclusion_local.isLocallyInjective.comp_right hji.continuous hji.injective
  exact hp.exists_finite_double_relation_complex s.compatible K hK hlocal

end Geometry.OriginalPLTower
