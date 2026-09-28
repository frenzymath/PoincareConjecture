import Mathlib.Geometry.Manifold.Diffeomorph



open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.HomeomorphTransport

variable {H M N : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [TopologicalSpace N] [ChartedSpace H M] (e : M ≃ₜ N)


@[reducible] def chartedSpace : ChartedSpace H N where
  atlas := (fun c => e.symm.toOpenPartialHomeomorph.trans c) '' atlas H M
  chartAt y := e.symm.toOpenPartialHomeomorph.trans (chartAt H (e.symm y))
  mem_chart_source y := by simp
  chart_mem_atlas y := ⟨chartAt H (e.symm y), chart_mem_atlas H _, rfl⟩

theorem chartAt_eq (y : N) :
    letI := chartedSpace (H := H) e
    chartAt H y = e.symm.toOpenPartialHomeomorph.trans (chartAt H (e.symm y)) := rfl

omit [ChartedSpace H M] in

theorem chart_transition (c c' : OpenPartialHomeomorph M H) :
    (e.symm.toOpenPartialHomeomorph.trans c).symm.trans
      (e.symm.toOpenPartialHomeomorph.trans c') = c.symm.trans c' := by
  ext z <;> simp [Function.comp_def]

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (r : ℕ∞ω)


theorem isManifold [IsManifold I r M] :
    letI := chartedSpace (H := H) e
    IsManifold I r N := by
  let := chartedSpace (H := H) e
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [chart_transition]
  exact StructureGroupoid.compatible (contDiffGroupoid r I) hc hc'


theorem contMDiff [IsManifold I r M] :
    letI := chartedSpace (H := H) e
    ContMDiff I I r e := by
  let := chartedSpace (H := H) e
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨e.continuous.continuousAt, ?_⟩
  have hid := (contMDiffAt_iff.mp
    ((contMDiff_id (I := I) (n := r)).contMDiffAt (x := x))).2
  simpa [extChartAt_coe, extChartAt_coe_symm, chartAt_eq e, Function.comp_def] using hid


theorem contMDiff_symm [IsManifold I r M] :
    letI := chartedSpace (H := H) e
    ContMDiff I I r e.symm := by
  let := chartedSpace (H := H) e
  intro y
  apply contMDiffAt_iff.mpr
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have hid := (contMDiffAt_iff.mp
    ((contMDiff_id (I := I) (n := r)).contMDiffAt (x := e.symm y))).2
  simpa [extChartAt_coe, extChartAt_coe_symm, chartAt_eq e, Function.comp_def] using hid


def diffeomorph [IsManifold I r M] :
    letI := chartedSpace (H := H) e
    Diffeomorph I I M N r := by
  letI := chartedSpace (H := H) e
  exact { e.toEquiv with
    contMDiff_toFun := contMDiff e I r
    contMDiff_invFun := contMDiff_symm e I r }

end Poincare.Manifold.HomeomorphTransport
