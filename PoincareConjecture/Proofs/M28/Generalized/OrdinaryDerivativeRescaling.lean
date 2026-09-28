import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalShiHomothetyCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
  {Q a : ℝ} {hQ : 0 < Q}



theorem ordinaryRescaling_curvatureDerivativeNorm
    (R : OrdinaryParabolicRescaling F Q hQ a) (s : ℝ) (m : ℕ) (x : M) :
    (R.flow.connection s).curvatureDerivativeNorm m x =
      (Real.sqrt Q)⁻¹ ^ (m + 2) *
        (F.connection (parabolicTimeInv Q a s)).curvatureDerivativeNorm m x := by
  let D := F.connection (parabolicTimeInv Q a s)
  let DQ := M13.scaleLeviCivitaData D Q hQ
  have hinv : ∀ y ∈ (univ : Set M),
      (mfderiv (𝓡 n) (𝓡 n) (id : M → M) y).IsInvertible := by
    intro y _
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hmetric : ∀ y ∈ (univ : Set M), ∀ v w : TangentSpace (𝓡 n) y,
      (R.flow.metric s).inner y v w =
        (M13.scaleSmoothMetric (F.metric (parabolicTimeInv Q a s)) Q hQ).inner y
          (mfderiv (𝓡 n) (𝓡 n) (id : M → M) y v)
          (mfderiv (𝓡 n) (𝓡 n) (id : M → M) y w) := by
    intro y _ v w
    simp only [mfderiv_id]
    change (R.flow.metric s).inner y v w =
      Q * (F.metric (parabolicTimeInv Q a s)).inner y v w
    exact R.metric_eq s y v w
  have hlocal := (R.flow.connection s).curvatureDerivativeNorm_eq_pullback DQ
    isOpen_univ contMDiff_id.contMDiffOn hinv hmetric m (mem_univ x)
  change (R.flow.connection s).curvatureDerivativeNorm m x =
    DQ.curvatureDerivativeNorm m x at hlocal
  rw [hlocal, scale_curvatureDerivativeNorm_eq]
  have hcancel : Q * (Real.sqrt Q)⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hQ.le, mul_inv_cancel₀ hQ.ne']
  rw [show 4 + m = 2 + (m + 2) by omega, pow_add, ← mul_assoc Q, hcancel, one_mul]

end PoincareConjecture.M28
