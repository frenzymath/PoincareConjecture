import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphSlope
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal NNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem sphere_height_oscillation_of_intrinsic_slope
    {h : UnitTwoSphere → ℝ} (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    {α : ℝ} (hα : 0 < α)
    (hslope : ∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
      |mvfderiv (𝓡 2) h q v| ≤ α * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v))
    (p q : UnitTwoSphere) : |h q - h p| ≤ α * Real.pi := by
  let g := Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2
  let K : ℝ≥0 := ⟨α, hα.le⟩
  have hnorm (x : UnitTwoSphere) (v : TangentSpace (𝓡 2) x) :
      g.tangentNorm x v = (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) x v) := by
    change Real.sqrt (g.inner x v v) = _
    rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner,
      RiemannianMetric.euclideanMetric_inner]
    exact (norm_eq_sqrt_real_inner _).symm
  have he := g.edist_le_mul_edist_of_derivative_bound
    (hsmooth.of_le (by simp)) (K := K) (show 0 < K from hα)
    (fun x v => by rw [hnorm]; exact hslope x v) q p
  have hg : g.edist q p ≤ ENNReal.ofReal Real.pi := by
    rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_edist_eq_angle (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (Real.arccos_le_pi _)
  have hbound : ENNReal.ofReal |h q - h p| ≤ ENNReal.ofReal (α * Real.pi) := by
    calc
      ENNReal.ofReal |h q - h p| = edist (h q) (h p) := by
        rw [edist_dist, Real.dist_eq]
      _ ≤ (K : ℝ≥0∞) * g.edist q p := he
      _ ≤ (K : ℝ≥0∞) * ENNReal.ofReal Real.pi := mul_le_mul' le_rfl hg
      _ = ENNReal.ofReal (α * Real.pi) := by
        rw [ENNReal.ofReal_mul hα.le]
        change _ = ENNReal.ofReal (K : ℝ) * ENNReal.ofReal Real.pi
        rw [ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα.le Real.pi_pos.le)).mp hbound

theorem coordinate_graph_height_bound
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {h : UnitTwoSphere → ℝ} (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {α : ℝ} (hα : 0 < α)
    (hslope : ∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
      |mvfderiv (𝓡 2) h q v| ≤ α * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v))
    {x : M} (hx : x ∈ range (fun q => N.coordinate_map (q, h q)))
    (q : UnitTwoSphere) : |h q - (N.coordinate_inverse x).2| ≤ α * Real.pi := by
  obtain ⟨p, rfl⟩ := hx
  rw [N.coordinate_inverse_coordinate_map ⟨mem_univ p, hdom p⟩]
  exact sphere_height_oscillation_of_intrinsic_slope hsmooth hα hslope p q

end PoincareConjecture.EpsilonNeck
