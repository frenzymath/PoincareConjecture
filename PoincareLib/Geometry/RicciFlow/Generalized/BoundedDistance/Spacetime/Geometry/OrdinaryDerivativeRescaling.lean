import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Local.Geometry.LocalShiHomothetyCurvature
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality

/-!
# Covariant curvature derivatives of an ordinary parabolic rescaling

The chosen M13 flow has the exact metric scaling at every real time.
Local-isometry naturality compares its genuine connection with the
constant-scale connection, giving the factor `sqrt(Q)^(-(m+2))`.
Morgan--Tian Definition 3.40, p. 61, and Proposition 5.14, pp. 90-91;
M28 derivation 74.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M28

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
  {Q a : ℝ} {hQ : 0 < Q}

/-- All covariant-curvature derivative norms have the exact parabolic
scale factor, for the actual selected M13 connection (derivation 74). -/
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

end PoincareMT.M28
