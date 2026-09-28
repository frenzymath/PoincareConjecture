import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.TraceRegularity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem continuous_curvatureDerivativeNorm (D : LeviCivitaData g) (k : ℕ) :
    Continuous (D.curvatureDerivativeNorm k) := by
  have hT := D.iteratedCovariantTensorDerivative_isSmooth D.riemannEvaluation_isSmooth_manifold k
  have h := (M04.contMDiff_tensorNorm_sq g hT).continuous.sqrt
  convert! h using 1
  funext x
  exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm

theorem curvatureDerivativeNorm_bounded_on_compact (D : LeviCivitaData g)
    (k : ℕ) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, D.curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_curvatureDerivativeNorm D k).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

theorem contMDiff_scalarCurvature (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  intro x
  have hT := (M04.isSmoothCovariantTensor_ricciEvaluation D).tensorTrace (g := g)
  have h := hT.contMDiffAt_apply (x := x) (X := fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i)
  convert! h using 1

theorem scalarCurvature_bounds_on_compact (D : LeviCivitaData g)
    {K : Set M} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, 0 < D.scalarCurvature x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      C⁻¹ ≤ D.scalarCurvature x ∧ D.scalarCurvature x ≤ C := by
  have hcont : ContinuousOn D.scalarCurvature K :=
    (contMDiff_scalarCurvature D).continuous.continuousOn
  obtain ⟨A, hA⟩ := hK.bddAbove_image hcont
  have hinv : ContinuousOn (fun x => (D.scalarCurvature x)⁻¹) K :=
    hcont.inv₀ (fun x hx => ne_of_gt (hpos x hx))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hinv
  refine ⟨max 1 (max A B), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  constructor
  · apply (inv_le_comm₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (hpos x hx)).mpr
    exact (hB ⟨x, hx, rfl⟩).trans ((le_max_right A B).trans (le_max_right _ _))
  · exact (hA ⟨x, hx, rfl⟩).trans ((le_max_left A B).trans (le_max_right _ _))

end PoincareConjecture.M34
