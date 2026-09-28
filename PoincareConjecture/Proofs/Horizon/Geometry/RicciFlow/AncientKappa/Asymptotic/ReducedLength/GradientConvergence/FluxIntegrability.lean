import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.EnergyIntegrability
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.FluxProducts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u
namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem integrableOn_coordinate_gradient_pairing (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) (hφ : ContDiff ℝ ∞ φ) :
    IntegrableOn (fun x => g.pullbackVolumeDensity e x *
      fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ u x))) O := by
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
  have hχ (i : Fin n) : MemLp
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) ∞ (volume.restrict O) := by
    have hc := ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := EuclideanSpace.single i (1 : ℝ)))).continuous
    obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn hc.continuousOn
    apply memLp_top_of_bound hc.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact hC x (subset_closure hx)
  simpa only [LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing] using
    Poincare.Analysis.Elliptic.integrable_gradient_pairing_of_lipschitz hO hu hA hχ

end PoincareConjecture.RiemannianMetric
