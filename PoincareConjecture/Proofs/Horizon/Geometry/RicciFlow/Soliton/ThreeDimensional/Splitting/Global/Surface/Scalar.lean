import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.SolitonEquation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Roundness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Flow









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem scalarCurvature_eq_twice_scale_of_parallel_soliton
    (D : LeviCivitaData g) (hc : MetricComplete g)
    {r φ : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient D r) (hz : HasZeroHessian D r)
    (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 φ)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      D.ricci x v w + D.hessian φ x v w = lambda * g.inner x v w)
    (hop : ∀ x, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x, D.curvatureTensorNorm x ≠ 0) :
    ∀ x, D.scalarCurvature x = 2 * lambda := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun y (_ : y ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu y
  let := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
  let h := regularLevelMetric hr (⊤ : Opens M) hreg 0 g
  obtain ⟨hne, hconn, hcomplete, Φ, e, _, _, _, _, _, hscalar, hnorm, hopN, _⟩ :=
    exists_parallelGradient_productIsometry_curvature hc hr hu hz
  let : ConnectedSpace (zeroLevelSet r) := hconn
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 (φ ∘ zeroLevelIncl r) :=
    hφ.comp ((contMDiff_openLevelIncl hr (⊤ : Opens M) hreg 2 0).of_le
      (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
  have hsolN := parallelGradient_factor_soliton_equation hr hu hz hφ hsol
  have hnonflatN : ∃ y, h.leviCivitaData.curvatureTensorNorm y ≠ 0 := by
    obtain ⟨x, hx⟩ := hnonflat
    exact ⟨(e.symm x).1, by rw [hnorm]; exact hx⟩
  let : CompactSpace (zeroLevelSet r) :=
    h.leviCivitaData.compactSpace_of_surface_shrinker hcomplete hf hlambda hsolN
      (hopN hop) hnonflatN
  have hround := h.leviCivitaData.constantPositiveSectionalCurvature_of_surface_shrinker
    hcomplete hf hlambda hsolN (hopN hop) hnonflatN
  intro x
  exact (hscalar x).symm.trans
    (h.leviCivitaData.scalar_eq_twice_scale_of_compact_round_soliton
      hf hsolN hround (e.symm x).1)

end PoincareConjecture.RiemannianMetric
