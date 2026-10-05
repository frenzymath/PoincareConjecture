import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialEstimates.EndTranslation
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants

/-!
# Curvature transport along an arbitrary cylindrical end

Morgan-Tian Lemma 12.3, pp. 294-295. The actual local end translations
preserve scalar curvature and the geometric norm of every iterated
covariant curvature derivative. In particular every positive-height
value agrees with a value on the compact height-one sphere.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

set_option backward.isDefEq.respectTransparency false in
/-- Every covariant curvature derivative norm is constant along an axial
line of the supplied positive end (Lemma 12.3, pp. 294-295). -/
theorem end_curvatureDerivativeNorm_translate (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) (s : ℝ) {z : StandardCylinderSpace}
    (hz : 0 < z.2) (hsz : 0 < z.2 + s) (k : ℕ) :
    D.curvatureDerivativeNorm k (e.coordinate z) =
      D.curvatureDerivativeNorm k (e.coordinate (z.1, z.2 + s)) := by
  obtain ⟨U, hU, hzU, hf, hmetric⟩ := endAxialTranslation_local_isometry e s hz hsz
  have hinv : ∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x).IsInvertible := by
    intro x hx
    have hbij := g.mfderiv_bijective_of_pullback_eq g x
      (fun u v => (hmetric x hx u v).symm)
    let L : StandardCapSpace →L[ℝ] StandardCapSpace :=
      mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x
    change L.IsInvertible
    exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
  have h := D.curvatureDerivativeNorm_eq_pullback D hU hf hinv hmetric k hzU
  simpa only [endAxialTranslation_coordinate e s hz.le] using h

/-- Scalar curvature is constant along an axial line of the supplied
positive end (Lemma 12.3, pp. 294-295). -/
theorem end_scalarCurvature_translate (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) (s : ℝ) {z : StandardCylinderSpace}
    (hz : 0 < z.2) (hsz : 0 < z.2 + s) :
    D.scalarCurvature (e.coordinate z) =
      D.scalarCurvature (e.coordinate (z.1, z.2 + s)) := by
  obtain ⟨U, hU, hzU, hf, hmetric⟩ := endAxialTranslation_local_isometry e s hz hsz
  have h := D.scalarCurvature_eq_of_local_isometry D hU hf hmetric hzU
  simpa only [endAxialTranslation_coordinate e s hz.le] using h

end PoincareMT.M34
