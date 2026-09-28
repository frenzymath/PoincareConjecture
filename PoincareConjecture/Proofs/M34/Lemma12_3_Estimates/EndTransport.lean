import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndTranslation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants










set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

set_option backward.isDefEq.respectTransparency false in


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



theorem end_scalarCurvature_translate (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) (s : ℝ) {z : StandardCylinderSpace}
    (hz : 0 < z.2) (hsz : 0 < z.2 + s) :
    D.scalarCurvature (e.coordinate z) =
      D.scalarCurvature (e.coordinate (z.1, z.2 + s)) := by
  obtain ⟨U, hU, hzU, hf, hmetric⟩ := endAxialTranslation_local_isometry e s hz hsz
  have h := D.scalarCurvature_eq_of_local_isometry D hU hf hmetric hzU
  simpa only [endAxialTranslation_coordinate e s hz.le] using h

end PoincareConjecture.M34
