import PoincareConjecture.Proofs.M10.ChartLipschitz
import PoincareConjecture.Proofs.M10.NullTransport
import Mathlib.Analysis.Calculus.Rademacher










set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in

theorem calibratedMetricVolume_nondifferentiability_eq_zero
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ∀ q : M,
      ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S ∧ extChartAt (𝓡 n) q q ∈ S ∧
        S ⊆ (extChartAt (𝓡 n) q).target ∧
        ∃ K : ℝ≥0, LipschitzOnWith K (f ∘ (extChartAt (𝓡 n) q).symm) S) :
    calibratedMetricVolume g {q | ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f q} = 0 := by
  apply measure_null_of_locally_null
  intro q _hq
  obtain ⟨S, hSopen, hqS, _hStarget, K, hLip⟩ := hf q
  obtain ⟨r, hr, _hrtarget, C, hchart⟩ := inverseChart_local_lipschitz g q
  let e := extChartAt (𝓡 n) q
  let U := S ∩ Metric.ball (e q) r
  have hUopen : IsOpen U := hSopen.inter Metric.isOpen_ball
  have hqU : e q ∈ U := ⟨hqS, Metric.mem_ball_self hr⟩
  let B := {y | y ∈ U ∧ ¬ DifferentiableAt ℝ (f ∘ e.symm) y}
  have hBnull : volume B = 0 := by
    have hgood : ∀ᵐ y ∂volume, y ∈ U → DifferentiableAt ℝ (f ∘ e.symm) y := by
      filter_upwards [LipschitzOnWith.ae_differentiableWithinAt_of_mem (μ := volume)
        (hLip.mono (show U ⊆ S from inter_subset_left))] with y hy hyU
      exact (hy hyU).differentiableAt (hUopen.mem_nhds hyU)
    simpa only [Classical.not_imp] using ae_iff.mp hgood
  have himage : calibratedMetricVolume g (e.symm '' B) = 0 :=
    calibratedMetricVolume_image_eq_zero_of_lipschitz g
      (fun _ hy ↦ hy.1.2) hBnull hchart
  let V := e.source ∩ e ⁻¹' U
  have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 n) q)
    ((continuousAt_extChartAt (I := 𝓡 n) q).preimage_mem_nhds (hUopen.mem_nhds hqU))
  refine ⟨V ∩ {x | ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f x},
    inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin, ?_⟩
  apply measure_mono_null _ himage
  intro x hx
  refine ⟨e x, ⟨hx.1.2, ?_⟩, e.left_inv hx.1.1⟩
  intro hdiff
  apply hx.2
  apply (mdifferentiableAt_iff_source_of_mem_source (I := 𝓡 n)
    (I' := 𝓘(ℝ, ℝ)) (f := f) (x := q)
    (by simpa only [← extChartAt_source (𝓡 n)] using hx.1.1)).mpr
  simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ]
    using hdiff.mdifferentiableAt

end PoincareConjecture.M10
