import PoincareConjecture.Proofs.M10.ChartLipschitz
import PoincareConjecture.Proofs.M10.NullTransport
import Mathlib.MeasureTheory.Function.Jacobian









set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in

theorem calibratedMetricVolume_criticalValues_eq_zero
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    (hf : MDifferentiable (𝓡 n) (𝓡 n) f) :
    calibratedMetricVolume g (f '' {x | ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)}) = 0 := by
  apply measure_null_of_locally_null
  intro q _hq
  obtain ⟨r, hr, _hrtarget, C, hchart⟩ := inverseChart_local_lipschitz g q
  let e := extChartAt (𝓡 n) q
  let U := Metric.ball (e q) r
  let V := e.source ∩ e ⁻¹' U
  have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 n) q)
    ((continuousAt_extChartAt (I := 𝓡 n) q).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr))
  let A := {x | ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) ∧ f x ∈ V}
  have hcoord : ∀ x ∈ A, DifferentiableAt ℝ (e ∘ f) x := by
    intro x hx
    have he : MDifferentiableAt (𝓡 n) (𝓡 n) e (f x) :=
      mdifferentiableAt_extChartAt (by
        simpa only [← extChartAt_source (𝓡 n)] using hx.2.1)
    exact (he.comp x (hf x)).differentiableAt
  have hdet : ∀ x ∈ A, (fderiv ℝ (e ∘ f) x).det = 0 := by
    intro x hx
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hker
    have hinj : Function.Injective (fderiv ℝ (e ∘ f) x) := LinearMap.ker_eq_bot.mp hker
    have he : MDifferentiableAt (𝓡 n) (𝓡 n) e (f x) :=
      mdifferentiableAt_extChartAt (by
        simpa only [← extChartAt_source (𝓡 n)] using hx.2.1)
    have hchain := mfderiv_comp x he (hf x)
    rw [mfderiv_eq_fderiv] at hchain
    have hdf : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x) := by
      intro v w hvw
      apply hinj
      rw [hchain]
      exact congrArg (mfderiv (𝓡 n) (𝓡 n) e (f x)) hvw
    exact hx.1 ⟨hdf, LinearMap.injective_iff_surjective.mp hdf⟩
  have hnull : volume ((e ∘ f) '' A) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx ↦ (hcoord x hx).hasFDerivAt.hasFDerivWithinAt) hdet
  have himage : calibratedMetricVolume g (e.symm '' ((e ∘ f) '' A)) = 0 :=
    calibratedMetricVolume_image_eq_zero_of_lipschitz g
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.2.2) hnull hchart
  refine ⟨V ∩ f '' {x | ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)},
    inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin, ?_⟩
  apply measure_mono_null _ himage
  rintro y ⟨hyV, x, hx, rfl⟩
  exact ⟨e (f x), ⟨x, ⟨hx, hyV⟩, rfl⟩, e.left_inv hyV.1⟩

end PoincareConjecture.M10
