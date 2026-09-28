import PoincareConjecture.Proofs.M60.Mathlib.LocalAlmostEverywhere
import PoincareConjecture.Proofs.M40.Mathlib.LocalSmoothLipschitz
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv










set_option autoImplicit false

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M60




theorem ae_mdifferentiableAt_of_lipschitzOn
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle F (TangentSpace I : M → Type _)]
    [IsRiemannianManifold I M]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → M} {S : Set E} (hS : IsOpen S) {K : ℝ≥0} (hf : LipschitzOnWith K f S) :
    ∀ᵐ x ∂μ, x ∈ S → MDifferentiableAt 𝓘(ℝ, E) I f x := by
  apply ae_imp_of_locally_ae μ (HereditarilyLindelofSpace.isLindelof S)
  intro x hx
  let e := extChartAt I (f x)
  have he : ContMDiffAt I 𝓘(ℝ, F) 1 e (f x) := contMDiffAt_extChartAt
  obtain ⟨A, -, V, hV, hLip⟩ := M40.exists_lipschitzOn_nhds_of_contMDiffAt he
  have hfc : ContinuousAt f x := (hf.continuousOn x hx).continuousAt (hS.mem_nhds hx)
  have hn : S ∩ f ⁻¹' (V ∩ (chartAt H (f x)).source) ∈ 𝓝 x :=
    inter_mem (hS.mem_nhds hx) (hfc.preimage_mem_nhds
      (inter_mem hV ((chartAt H (f x)).open_source.mem_nhds (mem_chart_source H (f x)))))
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hn
  refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
  have hcomp : LipschitzOnWith (A * K) (e ∘ f) U :=
    hLip.comp (hf.mono (fun _ hy => (hUsub hy).1)) (fun _ hy => (hUsub hy).2.1)
  filter_upwards [hcomp.ae_differentiableWithinAt_of_mem (μ := μ)] with y hy hyU
  have hd := (hy hyU).differentiableAt (hUopen.mem_nhds hyU)
  apply (mdifferentiableAt_iff_target_of_mem_source (I := 𝓘(ℝ, E))
    (I' := I) (hUsub hyU).2.2).mpr
  exact ⟨(hf.continuousOn y (hUsub hyU).1).continuousAt
    (hS.mem_nhds (hUsub hyU).1), hd.mdifferentiableAt⟩

end PoincareConjecture.M60
