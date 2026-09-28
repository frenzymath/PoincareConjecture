import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.MaximalBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.NormalNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.Curvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem scalarCurvature_center_eq_zero_of_unit_density
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R : ℝ} (hR : 0 < R)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R, g.IsGeodesicOn (fun s : ℝ => e (s • v))
      {s | s • v ∈ Metric.ball 0 R})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (hi : ∀ v ∈ Metric.ball 0 R,
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v))
    (hρ : ∀ v ∈ Metric.ball 0 R, g.pullbackVolumeDensity e v = 1)
    (hRic : ∀ v : TangentSpace (𝓡 (m + 1)) (e 0), 0 ≤ D.ricci (e 0) v v) :
    D.scalarCurvature (e 0) = 0 := by
  have hunit := g.ricci_center_unit_eq_zero_of_pullbackVolumeDensity_eq_one D hm
    Metric.isOpen_ball (Metric.mem_ball_self hR) he hgeo hmetric
    (Filter.mem_of_superset (Metric.ball_mem_nhds _ hR) hi)
    (Filter.mem_of_superset (Metric.ball_mem_nhds _ hR) hρ) hRic
  have hsurj : Function.Surjective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0) := by
    let f : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0).toLinearMap
    exact LinearMap.surjective_of_injective (f := f) (hi 0 (Metric.mem_ball_self hR))
  have hscale (c : ℝ) (v : TangentSpace (𝓡 (m + 1)) (e 0)) :
      D.ricci (e 0) (c • v) (c • v) = c ^ 2 * D.ricci (e 0) v v := by
    unfold LeviCivitaData.ricci
    simp_rw [← D.curvatureTensor_bilinear_first_third_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  have hall (v : TangentSpace (𝓡 (m + 1)) (e 0)) : D.ricci (e 0) v v = 0 := by
    obtain ⟨u, rfl⟩ := hsurj v
    by_cases hu : u = 0
    · subst u
      simpa only [map_zero, zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul] using hscale 0 0
    · have H := hunit (‖u‖⁻¹ • u) (norm_smul_inv_norm hu)
      rw [map_smul, hscale] at H
      exact (mul_eq_zero.mp H).resolve_left (pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr hu)))
  unfold LeviCivitaData.scalarCurvature
  simp only [hall, Finset.sum_const_zero]

theorem curvatureTensor_eq_zero_of_maximal_volume_growth
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hn : 2 ≤ n) (hc : MetricComplete g)
    (hoperator : ∀ x : M, D.NonnegativeCurvatureOperator x)
    (p : M)
    (hvolume : Tendsto
      (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      atTop (𝓝 (euclideanUnitBallVolume n))) :
    ∀ (x : M) (u v w z : TangentSpace (𝓡 n) x),
      D.curvatureTensor x u v w z = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    have hm : 0 < m := by omega
    have hRic (x : M) (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ D.ricci x v v :=
      D.ricci_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v
    have hballs := g.volumeMeasure_ball_eq_euclidean_of_maximal_asymptotic_volume
      D (by omega : 1 ≤ m + 1) hc hRic p hvolume
    intro x u v w z
    obtain ⟨R, hR, e, he0, he, hmetric, hgeo, hi, hinj, himage⟩ :=
      g.exists_normal_neighborhood_of_metricComplete hc x
    have hρ := g.pullbackVolumeDensity_eq_one_of_ball_volume_eq D hm hR he hgeo
      hmetric hi hinj (by simpa only [he0] using himage R hR le_rfl) hRic
      (hballs (e 0) hR)
    have hscalar := scalarCurvature_center_eq_zero_of_unit_density g D hm hR he hgeo
      hmetric hi hρ (hRic (e 0))
    rw [he0] at hscalar
    exact D.curvatureTensor_eq_zero_of_nonnegative_curvatureOperator_of_scalar_eq_zero
      x (hoperator x) hscalar u v w z

end PoincareConjecture.RiemannianMetric
