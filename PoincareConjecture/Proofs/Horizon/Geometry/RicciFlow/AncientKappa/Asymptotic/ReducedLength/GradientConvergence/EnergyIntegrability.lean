import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.ComparisonTests
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Products


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u
namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem integrableOn_coordinate_gradient_energy (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) :
    IntegrableOn (fun x => g.pullbackVolumeDensity e x *
      fderiv ℝ u x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x))) O := by
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hOc.measure_lt_top⟩
  have hA (i j : Fin n) : MemLp
      (fun x => LeviCivitaData.Dirichlet.divergenceCoefficients g e x i j)
      ∞ (volume.restrict O) := by
    have hc := (LeviCivitaData.Dirichlet.contDiffOn_divergenceCoefficients
      (g := g) e he hei i j).continuousOn.mono hOs
    obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn hc
    apply memLp_top_of_bound ((hc.mono subset_closure).aestronglyMeasurable hO.measurableSet) C
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact hC x (subset_closure hx)
  simpa only [LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing] using
    Poincare.Analysis.Elliptic.integrable_gradient_quadratic_of_lipschitz hO hu hA

end PoincareConjecture.RiemannianMetric
