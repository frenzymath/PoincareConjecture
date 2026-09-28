import PoincareConjecture.Proofs.M10.ChartLipschitz
import PoincareConjecture.Proofs.M10.NullTransport
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M49

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in

theorem calibratedMetricVolume_image_eq_zero_of_mdifferentiableOn
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (hf : MDifferentiableOn (𝓡 n) (𝓡 n) f A) (hA : volume A = 0) :
    calibratedMetricVolume g (f '' A) = 0 := by
  apply measure_null_of_locally_null
  intro q _hq
  obtain ⟨r, hr, _hrtarget, C, hchart⟩ := M10.inverseChart_local_lipschitz g q
  let e := extChartAt (𝓡 n) q
  let U := Metric.ball (e q) r
  let V := e.source ∩ e ⁻¹' U
  have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 n) q)
    ((continuousAt_extChartAt (I := 𝓡 n) q).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr))
  let B := A ∩ f ⁻¹' V
  have hcoord : DifferentiableOn ℝ (e ∘ f) B := by
    intro x hx
    have he : MDifferentiableAt (𝓡 n) (𝓡 n) e (f x) :=
      mdifferentiableAt_extChartAt (by
        simpa only [← extChartAt_source (𝓡 n)] using hx.2.1)
    exact (he.comp_mdifferentiableWithinAt x
      ((hf x hx.1).mono inter_subset_left)).differentiableWithinAt
  have hnull : volume ((e ∘ f) '' B) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hcoord
      (measure_mono_null inter_subset_left hA)
  have himage : calibratedMetricVolume g (e.symm '' ((e ∘ f) '' B)) = 0 :=
    M10.calibratedMetricVolume_image_eq_zero_of_lipschitz g
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.2.2) hnull hchart
  refine ⟨V ∩ f '' A,
    inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin, ?_⟩
  apply measure_mono_null _ himage
  rintro y ⟨hyV, x, hx, rfl⟩
  exact ⟨e (f x), ⟨x, ⟨hx, hyV⟩, rfl⟩, e.left_inv hyV.1⟩

end PoincareConjecture.M49
