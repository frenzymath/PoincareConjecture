import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Matrix
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Density

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

theorem abs_det_transverse_radialDifferential
    (g : RiemannianMetric (m + 1) M)
    (e : EuclideanSpace ℝ (Fin (m + 1)) → M)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    {t : ℝ} (ht : 0 < t)
    (P : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ]
      TangentSpace (𝓡 (m + 1)) (e (t • b 0)))
    (hP : ∀ u v, g.inner (e (t • b 0)) (P u) (P v) = inner ℝ u v)
    (hrad : mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0) (b 0) = P (b 0)) :
    |((LinearMap.toMatrix b.toBasis b.toBasis
      (t • (P.symm.toContinuousLinearMap.comp
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0))) :
          EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (m + 1))).toLinearMap).submatrix
          Fin.succ Fin.succ).det| =
      t ^ m * g.pullbackVolumeDensity e (t • b 0) := by
  let A : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (m + 1)) :=
    t • (P.symm.toContinuousLinearMap.comp
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0)))
  have ha : A (b 0) = t • b 0 := by
    change t • P.symm (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0) (b 0)) = _
    rw [hrad, P.symm_apply_apply]
  have hd := congrArg abs (det_eq_radial_mul_transverse b A t ha)
  rw [abs_mul, abs_of_pos ht, LinearMap.det_toMatrix] at hd
  have hfull := g.abs_det_scaled_differential_eq e (t • b 0) P hP ht.le
  change |A.det| = _ at hfull
  change |A.det| = _ at hd
  rw [hfull, pow_succ] at hd
  have hdt : t * (t ^ m * g.pullbackVolumeDensity e (t • b 0)) =
      t * |((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
        Fin.succ Fin.succ).det| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hd
  exact (mul_left_cancel₀ ht.ne' hdt).symm

theorem abs_det_transverse_radialDifferential_of_isInvertible
    (g : RiemannianMetric (m + 1) M)
    (e : EuclideanSpace ℝ (Fin (m + 1)) → M)
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    {t : ℝ} (ht : 0 < t)
    (P : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ]
      TangentSpace (𝓡 (m + 1)) (e (t • b 0)))
    (hi : P.IsInvertible)
    (hP : ∀ u v, g.inner (e (t • b 0)) (P u) (P v) = inner ℝ u v)
    (hrad : mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0) (b 0) = P (b 0)) :
    |((LinearMap.toMatrix b.toBasis b.toBasis
      (P.inverse.comp (t • mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0)) :
        EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).toLinearMap
        ).submatrix Fin.succ Fin.succ).det| =
      t ^ m * g.pullbackVolumeDensity e (t • b 0) := by
  obtain ⟨Q, hQ⟩ := hi
  have hQa (u) : Q u = P u := congrArg (fun A => A u) hQ
  have heq : (P.inverse.comp (t • mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0)) :
      EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) =
      t • Q.symm.toContinuousLinearMap.comp (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0)) := by
    apply ContinuousLinearMap.ext
    intro u
    change P.inverse (t • mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • b 0) u) = _
    rw [map_smul, ← hQ, ContinuousLinearMap.inverse_equiv]
    rfl
  rw [heq]
  apply g.abs_det_transverse_radialDifferential e b ht Q
  · intro u v
    simpa only [hQa] using hP u v
  · simpa only [hQa] using hrad

end PoincareConjecture.RiemannianMetric
