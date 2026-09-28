import PoincareConjecture.Proofs.M10.ChartLipschitz
import PoincareConjecture.Proofs.M10.NullTransport
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]



theorem comparison_nondifferentiability_null
    (g : RiemannianMetric n M) {f : M → ℝ} (A : Set M)
    (hf : ∀ q ∈ A,
      ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S ∧ extChartAt (𝓡 n) q q ∈ S ∧
        S ⊆ (extChartAt (𝓡 n) q).target ∧
        ∃ K : ℝ≥0, LipschitzOnWith K (f ∘ (extChartAt (𝓡 n) q).symm) S) :
    calibratedMetricVolume g
      {q | q ∈ A ∧ ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f q} = 0 := by
  apply measure_null_of_locally_null
  intro q hq
  obtain ⟨S, hSopen, hqS, _, K, hLip⟩ := hf q hq.1
  obtain ⟨r, hr, _, C, hchart⟩ := M10.inverseChart_local_lipschitz g q
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
    M10.calibratedMetricVolume_image_eq_zero_of_lipschitz g
      (fun _ hy => hy.1.2) hBnull hchart
  let V := e.source ∩ e ⁻¹' U
  have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 n) q)
    ((continuousAt_extChartAt (I := 𝓡 n) q).preimage_mem_nhds (hUopen.mem_nhds hqU))
  refine ⟨V ∩ {x | x ∈ A ∧ ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f x},
    inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin, ?_⟩
  apply measure_mono_null _ himage
  intro x hx
  refine ⟨e x, ⟨hx.1.2, ?_⟩, e.left_inv hx.1.1⟩
  intro hdiff
  apply hx.2.2
  apply (mdifferentiableAt_iff_source_of_mem_source (I := 𝓡 n)
    (I' := 𝓘(ℝ, ℝ)) (f := f) (x := q)
    (by simpa only [← extChartAt_source (𝓡 n)] using hx.1.1)).mpr
  simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ]
    using hdiff.mdifferentiableAt



theorem survival_criticalValues_null
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (hf : ∀ x ∈ D, MDifferentiableAt (𝓡 n) (𝓡 n) f x) :
    calibratedMetricVolume g
      (f '' {x | x ∈ D ∧ ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)}) = 0 := by
  apply measure_null_of_locally_null
  intro q _
  obtain ⟨r, hr, _, C, hchart⟩ := M10.inverseChart_local_lipschitz g q
  let e := extChartAt (𝓡 n) q
  let U := Metric.ball (e q) r
  let V := e.source ∩ e ⁻¹' U
  have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 n) q)
    ((continuousAt_extChartAt (I := 𝓡 n) q).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr))
  let A := {x | (x ∈ D ∧ ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) ∧ f x ∈ V}
  have hcoord : ∀ x ∈ A, DifferentiableAt ℝ (e ∘ f) x := by
    intro x hx
    have he : MDifferentiableAt (𝓡 n) (𝓡 n) e (f x) :=
      mdifferentiableAt_extChartAt (by
        simpa only [← extChartAt_source (𝓡 n)] using hx.2.1)
    exact (he.comp x (hf x hx.1.1)).differentiableAt
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
    have hchain := mfderiv_comp x he (hf x hx.1.1)
    rw [mfderiv_eq_fderiv] at hchain
    have hdf : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x) := by
      intro v w hvw
      apply hinj
      rw [hchain]
      exact congrArg (mfderiv (𝓡 n) (𝓡 n) e (f x)) hvw
    exact hx.1.2 ⟨hdf, LinearMap.injective_iff_surjective.mp hdf⟩
  have hnull : volume ((e ∘ f) '' A) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => (hcoord x hx).hasFDerivAt.hasFDerivWithinAt) hdet
  have himage : calibratedMetricVolume g (e.symm '' ((e ∘ f) '' A)) = 0 :=
    M10.calibratedMetricVolume_image_eq_zero_of_lipschitz g
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.2.2) hnull hchart
  refine ⟨V ∩ f '' {x | x ∈ D ∧ ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)},
    inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin, ?_⟩
  apply measure_mono_null _ himage
  rintro y ⟨hyV, x, hx, rfl⟩
  exact ⟨e (f x), ⟨x, ⟨hx, hyV⟩, rfl⟩, e.left_inv hyV.1⟩

end PoincareConjecture.Proofs.M46
