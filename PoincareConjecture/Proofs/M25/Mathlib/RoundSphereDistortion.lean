import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture
open scoped Manifold ContDiff ENNReal

namespace Poincare.Geometry.Riemannian.SpaceForm




theorem roundSphereMetric_tangentNorm_eq_inclusion_norm {n : ℕ}
    (x : UnitSphere n) (v : TangentSpace (𝓡 n) x) :
    (roundSphereMetric n).tangentNorm x v =
      (norm : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun p : UnitSphere n => p.1) x v) := by
  change Real.sqrt ((roundSphereMetric n).inner x v v) = _
  rw [roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner]
  exact (norm_eq_sqrt_real_inner _).symm




theorem roundSphereMetric_edist_eq_vector_angle {n : ℕ} (hn : 1 ≤ n)
    (x y : UnitSphere n) :
    (roundSphereMetric n).edist x y =
      ENNReal.ofReal (InnerProductGeometry.angle x.1 y.1) := by
  have hnorm (p : UnitSphere n) : ‖p.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  have hsq : dist x y ^ 2 = 2 - 2 * inner ℝ x.1 y.1 := by
    simp only [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, hnorm]
    ring
  rw [roundSphereMetric_edist_eq_angle hn, InnerProductGeometry.angle,
    hnorm, hnorm, one_mul, div_one]
  congr 2
  linarith





theorem sphere_inner_distortion_of_diffeomorph_tangent_bounds
    {n : ℕ} (hn : 1 ≤ n)
    (e : Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere n) (UnitSphere n) ∞)
    {K : ℝ} (hK : 1 ≤ K)
    (hforward : ∀ (x : UnitSphere n) (v : TangentSpace (𝓡 n) x),
      (norm : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun p : UnitSphere n => p.1) (e x)
            (mfderiv (𝓡 n) (𝓡 n) e x v)) ≤
        K * (norm : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun p : UnitSphere n => p.1) x v))
    (hinverse : ∀ (x : UnitSphere n) (v : TangentSpace (𝓡 n) x),
      (norm : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun p : UnitSphere n => p.1) (e.symm x)
            (mfderiv (𝓡 n) (𝓡 n) e.symm x v)) ≤
        K * (norm : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun p : UnitSphere n => p.1) x v))
    (p q : UnitSphere n) :
    |inner ℝ (e p).1 (e q).1 - inner ℝ p.1 q.1| ≤ (K - 1) * Real.pi := by
  have hkpos : 0 < K := zero_lt_one.trans_le hK
  let g := roundSphereMetric n
  have hf := g.edist_le_mul_of_tangentNorm_mfderiv_le g
    (e.contMDiff.of_le (by simp)) hkpos (fun x v => by
      rw [roundSphereMetric_tangentNorm_eq_inclusion_norm,
        roundSphereMetric_tangentNorm_eq_inclusion_norm]
      exact hforward x v) p q
  have hi := g.edist_le_mul_of_tangentNorm_mfderiv_le g
    (e.symm.contMDiff.of_le (by simp)) hkpos (fun x v => by
      rw [roundSphereMetric_tangentNorm_eq_inclusion_norm,
        roundSphereMetric_tangentNorm_eq_inclusion_norm]
      exact hinverse x v) (e p) (e q)
  simp only [e.symm_apply_apply] at hi
  simp only [g, roundSphereMetric_edist_eq_vector_angle hn,
    ← ENNReal.ofReal_mul hkpos.le] at hf hi
  let a := InnerProductGeometry.angle p.1 q.1
  let b := InnerProductGeometry.angle (e p).1 (e q).1
  have ha : 0 ≤ a := InnerProductGeometry.angle_nonneg _ _
  have hb : 0 ≤ b := InnerProductGeometry.angle_nonneg _ _
  have haπ : a ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
  have hbπ : b ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
  have hab : b ≤ K * a :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hkpos.le ha)).mp hf
  have hba : a ≤ K * b :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hkpos.le hb)).mp hi
  have hangle : |b - a| ≤ (K - 1) * Real.pi := by
    have hA := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr haπ)
    have hB := mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hbπ)
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hnorm (x : UnitSphere n) : ‖x.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one (hnorm (e p)) (hnorm (e q)),
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one (hnorm p) (hnorm q)]
  exact (Real.abs_cos_sub_cos_le b a).trans hangle

end Poincare.Geometry.Riemannian.SpaceForm
