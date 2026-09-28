import PoincareConjecture.Proofs.M35.CapGeometry.RadialPointIdentification
import PoincareConjecture.Proofs.M35.CapGeometry.CurvatureDerivativeNorm
import PoincareConjecture.Proofs.M35.CapGeometry.RadialNormalization
import PoincareConjecture.Proofs.M13.Completeness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1



theorem rotational_curvatureDerivativeNorm_eq
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) (m : ℕ) :
    D.curvatureDerivativeNorm m (standardRotation A x) = D.curvatureDerivativeNorm m x := by
  let e := standardRotationDiffeomorph A
  exact (D.curvatureDerivativeNorm_eq_pullback D isOpen_univ e.contMDiff.contMDiffOn
    (fun y _ => ⟨e.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (fun y _ u v => (hrotation A y u v).symm) m (mem_univ x)).symm



theorem radial_curvatureDerivative_bound_of_ball_bound
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {d B : ℝ} (hd : 0 < d) (x : StandardCapSpace)
    (hbound : ∀ y ∈ g.ball x d, D.curvatureDerivativeNorm 1 y ≤ B)
    {r : ℝ} (hr : ‖x‖ ≤ r)
    (hlength : radialArclength g r - radialArclength g ‖x‖ ≤ d / 2) :
    D.curvatureDerivativeNorm 1 (r • e2) ≤ B := by
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  let e := standardRotationDiffeomorph A
  have he : MetricHomothety g g e 1 := by
    intro y u v
    change g.inner (standardRotation A y)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y v) = _
    simpa only [one_mul] using hrotation A y u v
  have hdist := M13.homothety_edist g g e 1 zero_lt_one he (‖x‖ • e2) (r • e2)
  have hAx : e (‖x‖ • e2) = x := hA
  rw [hAx, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hdist
  have hmem : e (r • e2) ∈ g.ball x d := by
    change g.edist x (e (r • e2)) < ENNReal.ofReal d
    rw [hdist]
    exact ((edist_axis_segment_le g hr).trans (ENNReal.ofReal_le_ofReal hlength)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hd).mpr (half_lt_self hd))
  have h := hbound (e (r • e2)) hmem
  change D.curvatureDerivativeNorm 1 (standardRotation A (r • e2)) ≤ B at h
  rw [rotational_curvatureDerivativeNorm_eq D hrotation A (r • e2) 1] at h
  exact h


theorem scaleSmoothMetric_rotation_invariant
    {g : RiemannianMetric 3 StandardCapSpace}
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (Q : ℝ) (hQ : 0 < Q) (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x u v : StandardCapSpace) :
    (M13.scaleSmoothMetric g Q hQ).inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
        (M13.scaleSmoothMetric g Q hQ).inner x u v := by
  simp only [M13.scaleSmoothMetric_inner, hrotation]


theorem scaleLeviCivitaData_nonnegative_sectional
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature) (Q : ℝ) (hQ : 0 < Q) :
    (M13.scaleLeviCivitaData D Q hQ).NonnegativeSectionalCurvature := by
  intro x u v
  have h := M13.homothety_curvatureTensor_eq g (M13.scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q
    (M13.identity_metricHomothety g Q hQ) D (M13.scaleLeviCivitaData D Q hQ) x u v u v
  change (M13.scaleLeviCivitaData D Q hQ).curvatureTensor x
    (mfderiv (𝓡 3) (𝓡 3) id x u) (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x u) (mfderiv (𝓡 3) (𝓡 3) id x v) = _ at h
  simp only [mfderiv_id] at h
  change (M13.scaleLeviCivitaData D Q hQ).curvatureTensor x u v u v =
    Q * D.curvatureTensor x u v u v at h
  rw [h]
  exact mul_nonneg hQ.le (hsec x u v)


theorem scaleSmoothMetric_complete
    (g : RiemannianMetric 3 StandardCapSpace) (hcomplete : MetricComplete g)
    (Q : ℝ) (hQ : 0 < Q) : MetricComplete (M13.scaleSmoothMetric g Q hQ) := by
  exact (M13.homothety_complete_iff g (M13.scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ)).mpr hcomplete

end PoincareConjecture.M35.Uniqueness
