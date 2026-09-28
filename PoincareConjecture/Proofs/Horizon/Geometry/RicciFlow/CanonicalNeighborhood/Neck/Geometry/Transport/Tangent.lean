import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem coordinate_flat_pullback :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ (z : RoundCylinderSpace), z ∈ N.cylinderDomain →
    ∀ (v w : TangentSpace (𝓡 3) z),
      g.inner (N.coordinate_map z)
        (mfderiv (𝓡 3) (𝓡 3) N.coordinate_map z v)
        (mfderiv (𝓡 3) (𝓡 3) N.coordinate_map z w) =
      roundCylinderPullback g N.coordinate_map z
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) roundCylinderModelDiffeomorph.symm z v)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) roundCylinderModelDiffeomorph.symm z w) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  intro z hz v w
  let e := roundCylinderModelDiffeomorph
  have hh := mfderiv_comp z
    ((N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt
      (by simp)) (e.symm.contMDiff.mdifferentiable (by simp) z)
  change mfderiv (𝓡 3) (𝓡 3) N.coordinate_map z = _ at hh
  change g.inner _ _ _ = g.inner _ _ _
  rw [hh]
  rfl

theorem coordinate_tangentNorm_bounds
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      a ^ 2 * EvolvingRoundCylinderMetric 0 z v v ≤
          roundCylinderPullback g N.coordinate_map z v v ∧
        roundCylinderPullback g N.coordinate_map z v v ≤
          b ^ 2 * EvolvingRoundCylinderMetric 0 z v v) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ z ∈ N.cylinderDomain, ∀ v : TangentSpace (𝓡 3) z,
      a * roundCylinderMetric.tangentNorm z v ≤
          g.tangentNorm (N.coordinate_map z) (mfderiv (𝓡 3) (𝓡 3) N.coordinate_map z v) ∧
        g.tangentNorm (N.coordinate_map z) (mfderiv (𝓡 3) (𝓡 3) N.coordinate_map z v) ≤
          b * roundCylinderMetric.tangentNorm z v := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  intro z hz v
  have hh := hbound z hz
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) roundCylinderModelDiffeomorph.symm z v)
  rw [← roundCylinderMetric_inner_flat z v v, ← N.coordinate_flat_pullback z hz v v] at hh
  unfold RiemannianMetric.tangentNorm
  constructor
  · simpa only [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha] using Real.sqrt_le_sqrt hh.1
  · simpa only [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb] using Real.sqrt_le_sqrt hh.2

theorem coordinate_map_mfderiv_inverse :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ x ∈ N.carrier, ∀ v : TangentSpace (𝓡 3) x,
      mfderiv (𝓡 3) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
        (mfderiv (𝓡 3) (𝓡 3) N.coordinate_inverse x v) = v := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  intro x hx v
  have hh := mfderiv_comp x
    ((N.coordinate_map_flat_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds (N.coordinate_inverse_mem x hx))).mdifferentiableAt
      (by simp))
    ((N.coordinate_inverse_flat_smooth.contMDiffAt (N.carrier_open.mem_nhds hx)).mdifferentiableAt
      (by simp))
  have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.coordinate_map_coordinate_inverse hy
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  exact (congrArg (fun L => L v) hh).symm

theorem coordinate_inverse_tangentNorm_le {a : ℝ} (ha : 0 < a) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    (∀ z ∈ N.cylinderDomain, ∀ v : TangentSpace (𝓡 3) z,
      a * roundCylinderMetric.tangentNorm z v ≤
        g.tangentNorm (N.coordinate_map z) (mfderiv (𝓡 3) (𝓡 3) N.coordinate_map z v)) →
    ∀ x ∈ N.carrier, ∀ v : TangentSpace (𝓡 3) x,
      roundCylinderMetric.tangentNorm (N.coordinate_inverse x)
        (mfderiv (𝓡 3) (𝓡 3) N.coordinate_inverse x v) ≤ a⁻¹ * g.tangentNorm x v := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  intro hbound x hx v
  have hh := hbound (N.coordinate_inverse x) (N.coordinate_inverse_mem x hx)
    (mfderiv (𝓡 3) (𝓡 3) N.coordinate_inverse x v)
  rw [N.coordinate_map_mfderiv_inverse x hx v, N.coordinate_map_coordinate_inverse hx] at hh
  exact (le_inv_mul_iff₀ ha).mpr hh

end PoincareConjecture.EpsilonNeck
