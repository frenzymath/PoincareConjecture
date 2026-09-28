import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M04.TensorNorm











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

set_option backward.isDefEq.respectTransparency false in


theorem endDoubleParametrization_mfderiv_isInvertible (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) {x : StandardCapSpace}
    (hx : x ∈ endTruncation e (L + 1)) :
    (mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hL i) x).IsInvertible := by
  have hbij := g.mfderiv_bijective_of_pullback_eq (endDoubleMetric e hL) x
    (fun u v => (endDoubleParametrization_metric e hL i hx u v).symm)
  let A : StandardCapSpace →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hL i) x
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2), rfl⟩



theorem endDoubleParametrization_curvatureDerivativeNorm (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) {L : ℝ} (hL : 1 < L)
    (D' : LeviCivitaData (endDoubleMetric e hL)) (i : Bool) (k : ℕ)
    {x : StandardCapSpace} (hx : x ∈ endTruncation e (L + 1)) :
    D.curvatureDerivativeNorm k x =
      D'.curvatureDerivativeNorm k (endDoubleParametrization e hL i x) :=
  D.curvatureDerivativeNorm_eq_pullback D'
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleParametrization_contMDiffOn e hL i)
    (fun _ hy => endDoubleParametrization_mfderiv_isInvertible e hL i hy)
    (fun _ hy u v => endDoubleParametrization_metric e hL i hy u v) k hx



theorem endDoubleParametrization_scalarCurvature (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) {L : ℝ} (hL : 1 < L)
    (D' : LeviCivitaData (endDoubleMetric e hL)) (i : Bool)
    {x : StandardCapSpace} (hx : x ∈ endTruncation e (L + 1)) :
    D.scalarCurvature x = D'.scalarCurvature (endDoubleParametrization e hL i x) :=
  D.scalarCurvature_eq_of_local_isometry D'
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleParametrization_contMDiffOn e hL i)
    (fun _ hy u v => endDoubleParametrization_metric e hL i hy u v) hx

set_option backward.isDefEq.respectTransparency false in


theorem endDouble_nonnegativeSectionalCurvature (D : LeviCivitaData g)
    (hD : D.NonnegativeSectionalCurvature) (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (D' : LeviCivitaData (endDoubleMetric e hL)) :
    D'.NonnegativeSectionalCurvature := by
  intro q u v
  obtain ⟨i, x, hx, rfl⟩ := endDoubleParametrization_cover e hL q
  have hbij := g.mfderiv_bijective_of_pullback_eq (endDoubleMetric e hL) x
    (fun a b => (endDoubleParametrization_metric e hL i hx a b).symm)
  obtain ⟨a, rfl⟩ := hbij.2 u
  obtain ⟨b, rfl⟩ := hbij.2 v
  rw [← D.curvatureTensor_eq_of_local_isometry D'
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleParametrization_contMDiffOn e hL i)
    (fun _ hy a b => endDoubleParametrization_metric e hL i hy a b) hx]
  exact hD x a b



theorem endDouble_curvatureDerivativeNorm_le (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) (k : ℕ) {C : ℝ}
    (hC : ∀ x : StandardCapSpace, D.curvatureDerivativeNorm k x ≤ C)
    {L : ℝ} (hL : 1 < L) (D' : LeviCivitaData (endDoubleMetric e hL))
    (q : EndDouble e hL) : D'.curvatureDerivativeNorm k q ≤ C := by
  obtain ⟨i, x, hx, rfl⟩ := endDoubleParametrization_cover e hL q
  rw [← endDoubleParametrization_curvatureDerivativeNorm D e hL D' i k hx]
  exact hC x



theorem endDouble_scalar_bounds (g0 : StandardInitialMetric) (E0 : StandardCapEstimate g0)
    {L : ℝ} (hL : 1 < L)
    (D : LeviCivitaData (endDoubleMetric g0.cylindrical_end hL))
    (q : EndDouble g0.cylindrical_end hL) :
    E0.scalar_constant⁻¹ ≤ D.scalarCurvature q ∧ D.scalarCurvature q ≤ E0.scalar_constant := by
  obtain ⟨i, x, hx, rfl⟩ := endDoubleParametrization_cover g0.cylindrical_end hL q
  rw [← endDoubleParametrization_scalarCurvature g0.connection g0.cylindrical_end hL D i hx]
  exact E0.scalar_bounds x



theorem endDouble_curvatureDerivative_bounds (g0 : StandardInitialMetric)
    (E0 : StandardCapEstimate g0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 < L)
      (D : LeviCivitaData (endDoubleMetric g0.cylindrical_end hL))
      (q : EndDouble g0.cylindrical_end hL), D.curvatureDerivativeNorm k q ≤ C := by
  obtain ⟨C, hC, hbound⟩ := E0.curvature_derivative_bounds k
  exact ⟨C, hC, fun _ hL D q =>
    endDouble_curvatureDerivativeNorm_le g0.connection g0.cylindrical_end k hbound hL D q⟩



theorem endDouble_curvatureTensorNorm_bound (g0 : StandardInitialMetric)
    (E0 : StandardCapEstimate g0) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : ℝ) (hL : 1 < L)
      (D : LeviCivitaData (endDoubleMetric g0.cylindrical_end hL))
      (q : EndDouble g0.cylindrical_end hL), D.curvatureTensorNorm q ≤ B := by
  obtain ⟨C, hC, hbound⟩ := endDouble_curvatureDerivative_bounds g0 E0 0
  refine ⟨C + 1, by linarith, ?_⟩
  intro L hL D q
  rw [← D.curvatureDerivativeNorm_zero]
  exact (hbound L hL D q).trans (by linarith)

end PoincareConjecture.M34
