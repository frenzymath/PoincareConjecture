import PoincareConjecture.Proofs.M35.CapGeometry.RadialUnitFieldBound
import PoincareConjecture.Proofs.M35.CapGeometry.RadialShapeDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem radialUnitField_contMDiffAt
    (g : RiemannianMetric 3 StandardCapSpace) {x : StandardCapSpace} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun y => Bundle.TotalSpace.mk' StandardCapSpace y
        (E := TangentSpace (𝓡 3)) (radialUnitField g y)) x := by
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using (radialUnitField_contDiffAt g hx).contMDiffAt⟩

theorem radialUnitField_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {G : RiemannianMetric 3 StandardCapSpace} (DG : LeviCivitaData G)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v)
    {f : M → StandardCapSpace} {x : M}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace (𝓡 3) y,
      g.inner y u v = G.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v))
    (hzero : f x ≠ 0) (b : ℝ)
    (hbound : ∀ w : StandardCapSpace,
      G.inner (f x) (DG.connection (radialUnitField G) (f x) w)
        (DG.connection (radialUnitField G) (f x) w) ≤ b ^ 2 * G.inner (f x) w w) :
    let Z := mpullback (𝓡 3) (𝓡 3) f (radialUnitField G)
    ContMDiffAt (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% Z) x ∧
      g.inner x (Z x) (Z x) = 1 ∧
      ∀ w : TangentSpace (𝓡 3) x,
        g.inner x (D.connection Z x w) (D.connection Z x w) ≤ b ^ 2 * g.inner x w w := by
  let Z := mpullback (𝓡 3) (𝓡 3) f (radialUnitField G)
  have hZ := radialUnitField_contMDiffAt G hzero
  have hi := hinv.self_of_nhds
  refine ⟨hZ.mpullback_vectorField_preimage hf hi (by simp), ?_, ?_⟩
  · rw [hmetric.self_of_nhds]
    simp only [mpullback, hi.self_apply_inverse]
    exact radialUnitField_unit G hrotation hzero
  · intro w
    have hc := D.connection_mpullback_of_metric_pullback DG hf hinv hmetric
      (hZ.mdifferentiableAt (by simp)) w
    change D.connection Z x w = _ at hc
    rw [hc, hmetric.self_of_nhds, hmetric.self_of_nhds]
    simp only [hi.self_apply_inverse]
    exact hbound (mfderiv (𝓡 3) (𝓡 3) f x w)

theorem radialUnitField_pullback_connection
    {g G : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (DG : LeviCivitaData G)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v)
    {f : StandardCapSpace → StandardCapSpace} {x : StandardCapSpace}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : StandardCapSpace,
      g.inner y u v = G.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v))
    (hzero : f x ≠ 0) (w : StandardCapSpace) :
    let Z : StandardCapSpace → StandardCapSpace :=
      fun y => (fderiv ℝ f y).inverse (radialUnitField G (f y))
    D.connection Z x w =
      (axisWarpingSlope G ‖f x‖ / axisWarpingRadius G ‖f x‖) •
        (w - g.inner x (Z x) w • Z x) := by
  have hi := hinv.self_of_nhds
  have hZ := (radialUnitField_contMDiffAt G hzero).mdifferentiableAt (by simp)
  have hc := D.connection_mpullback_of_metric_pullback DG hf hinv hmetric hZ w
  rw [radialUnitField_connection DG hrotation hzero] at hc
  let Z := mpullback (𝓡 3) (𝓡 3) f (radialUnitField G)
  have he : D.connection Z x w =
      (axisWarpingSlope G ‖f x‖ / axisWarpingRadius G ‖f x‖) •
        (@Sub.sub (TangentSpace (𝓡 3) x) _ w (g.inner x (Z x) w • Z x)) := by
    rw [hc, hmetric.self_of_nhds]
    simp only [Z, mpullback, map_smul, map_sub,
      hi.self_apply_inverse, hi.inverse_apply_self]
    rfl
  simpa only [Z, mpullback_eq_pullback, VectorField.pullback] using! he

theorem radial_shape_pullback_hasFDerivAt
    {g G : RiemannianMetric 3 StandardCapSpace}
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v)
    {f : StandardCapSpace → StandardCapSpace} {x : StandardCapSpace}
    (hf : DifferentiableAt ℝ f x)
    (hinv : (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible)
    (hmetric : ∀ u v : StandardCapSpace,
      g.inner x u v = G.inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v))
    (hzero : f x ≠ 0) :
    let Z : StandardCapSpace → StandardCapSpace :=
      fun y => (fderiv ℝ f y).inverse (radialUnitField G (f y))
    HasFDerivAt (fun y => axisWarpingSlope G ‖f y‖ / axisWarpingRadius G ‖f y‖)
      (-(radialMixedCurvatureFactor G ‖f x‖ / axisRadialCoefficient G ‖f x‖ +
        (axisWarpingSlope G ‖f x‖ / axisWarpingRadius G ‖f x‖) ^ 2) •
          g.euclideanCoefficients x (Z x)) x := by
  have h := (radial_shape_hasFDerivAt G hrotation hzero).comp x hf.hasFDerivAt
  dsimp only
  apply h.congr_fderiv
  ext w
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change _ = -(radialMixedCurvatureFactor G ‖f x‖ / axisRadialCoefficient G ‖f x‖ +
      (axisWarpingSlope G ‖f x‖ / axisWarpingRadius G ‖f x‖) ^ 2) *
        g.euclideanCoefficients x ((fderiv ℝ f x).inverse (radialUnitField G (f x))) w
  have hm (u v : StandardCapSpace) : g.euclideanCoefficients x u v =
      G.euclideanCoefficients (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) := by
    simpa only [mfderiv_eq_fderiv, RiemannianMetric.euclideanCoefficients] using! hmetric u v
  rw [hm]
  have hi : (fderiv ℝ f x).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using hinv
  rw [hi.self_apply_inverse]

end PoincareConjecture.M35.Uniqueness
