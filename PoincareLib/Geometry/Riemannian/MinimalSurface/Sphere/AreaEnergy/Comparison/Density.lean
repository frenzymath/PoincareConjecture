import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AreaEnergy.Comparison.Metric

/-!
# The actual regularized sphere densities

Morgan-Tian Lemma 18.10, printed pp. 424-426, with the area-to-energy
erratum. In the fixed stereographic chart the regularized Gram matrix is
the original Gram matrix plus delta times the round coordinate density.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The exact stereographic Gram matrix of the actual regularized metric.
Source: MT Lemma 18.10, pp. 424-426, area-to-energy erratum. -/
theorem m60SphereRegularizedMetric_gram (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (z : LoopPlane) (i j : Fin 2) :
    m60AreaGram (m60SphereRegularizedMetric g f hf delta hdelta) m60SphereParameter z i j =
      m60AreaGram g (f ∘ m60SphereParameter) z i j +
        delta * (16 / (‖z‖ ^ 2 + 4) ^ 2) *
          inner ℝ (EuclideanSpace.basisFun (Fin 2) ℝ i)
            (EuclideanSpace.basisFun (Fin 2) ℝ j) := by
  unfold m60AreaGram
  rw [m60SphereRegularizedMetric_inner,
    mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _),
    m60SphereParameter_inner]
  rw [mul_assoc]
  rfl

/-- Regularization adds delta times the round density to energy density.
Source: MT Lemma 18.10, pp. 424-426, area-to-energy erratum. -/
theorem m60SphereRegularizedMetric_energyDensity (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (z : LoopPlane) :
    m60SphereEnergyDensity (m60SphereRegularizedMetric g f hf delta hdelta) id z =
      m60SphereEnergyDensity g f z + delta * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  simp only [m60SphereEnergyDensity, Function.id_comp, m60EnergyDensity,
    Matrix.trace_fin_two, m60SphereRegularizedMetric_gram,
    real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one,
    one_pow, mul_one]
  ring

/-- The actual regularized determinant, including points where the
original differential is not injective. Source: MT Lemma 18.10, pp. 424-426. -/
theorem m60SphereRegularizedMetric_det (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (z : LoopPlane) :
    Matrix.det (m60AreaGram (m60SphereRegularizedMetric g f hf delta hdelta)
      m60SphereParameter z) =
      Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z) +
        2 * delta * (16 / (‖z‖ ^ 2 + 4) ^ 2) * m60SphereEnergyDensity g f z +
        delta ^ 2 * (16 / (‖z‖ ^ 2 + 4) ^ 2) ^ 2 := by
  simp only [Matrix.det_fin_two, m60SphereRegularizedMetric_gram,
    m60SphereEnergyDensity, m60EnergyDensity, Matrix.trace_fin_two]
  norm_num [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]
  ring

/-- The regularized area density has an integrable bound uniform for
delta at most one. Source: MT Lemma 18.10, pp. 424-426, erratum. -/
theorem m60SphereRegularizedMetric_areaDensity_bound (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1) (z : LoopPlane) :
    m60SphereAreaDensity (m60SphereRegularizedMetric g f hf delta hdelta) id z ≤
      m60SphereEnergyDensity g f z + (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  calc
    _ ≤ m60SphereEnergyDensity (m60SphereRegularizedMetric g f hf delta hdelta) id z :=
      m60AreaDensity_le_energyDensity _ _ _
    _ = m60SphereEnergyDensity g f z + delta * (16 / (‖z‖ ^ 2 + 4) ^ 2) :=
      m60SphereRegularizedMetric_energyDensity g f hf delta hdelta z
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hdelta'
        (show 0 ≤ 16 / (‖z‖ ^ 2 + 4) ^ 2 by positivity)

end PoincareMT
