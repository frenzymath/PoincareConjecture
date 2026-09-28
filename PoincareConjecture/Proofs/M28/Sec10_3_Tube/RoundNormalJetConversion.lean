import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundMetricEllipticity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.TensorCoordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

open PoincareConjecture
open PoincareConjecture.LeviCivitaData
open PoincareConjecture.CoordinateExponential



theorem christoffelBilinear_zero_of_gauss
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiff ℝ ∞ B)
    (hinv : ∀ y, (B y).IsInvertible)
    (hsymm : ∀ y u v, B y u v = B y v u)
    (hgauss : ∀ y w, B y y w = inner ℝ y w) :
    christoffelBilinear B 0 = 0 := by
  have hdiag (v : E) : christoffelBilinear B 0 v v = 0 := by
    simpa using christoffelBilinear_radial_eq_zero_of_gauss hB
      hinv hsymm hgauss v 0
  have hsym (u v : E) :
      christoffelBilinear B 0 u v = christoffelBilinear B 0 v u := by
    apply christoffelBilinear_symm
      ((hB.differentiable (by simp)).differentiableAt)
    exact Filter.Eventually.of_forall hsymm
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have huv := hdiag (u + v)
  have huu := hdiag u
  have hvv := hdiag v
  have huv' := hsym u v
  simp only [map_add, add_apply] at huv
  rw [huv'] at huv
  rw [huu, hvv] at huv
  have hcross : (christoffelBilinear B 0 v) u +
      (christoffelBilinear B 0 v) u = 0 := by
    simpa [add_assoc, add_left_comm, add_comm] using huv
  have hs : (2 : ℝ) • ((christoffelBilinear B 0 v) u) = 0 := by
    simpa [two_smul] using hcross
  have hcross' : (christoffelBilinear B 0 v) u = 0 :=
    (smul_eq_zero.mp hs).resolve_left (by norm_num)
  exact huv'.trans hcross'



theorem gauss_center_coordinate_connection_zero
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g)
    (hgauss : ∀ y w, g.euclideanCoefficients y y w = inner ℝ y w) :
    D.coordinateConnectionCoefficient 0 0 = 0 := by
  rw [D.coordinateConnectionCoefficient_model 0 0]
  exact christoffelBilinear_zero_of_gauss
    (contDiff_iff_contDiffAt.mpr (fun y => g.contDiffAt_euclideanCoefficients y))
    (fun y => g.inner_isInvertible y)
    (fun y u v => g.symm y u v) hgauss



theorem covariant_metric_error_eq_fderiv_of_zero_connection
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation 3 M 2}
    (hT : IsSmoothCovariantTensor T) (p x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3)) p).baseSet)
    (u : EuclideanSpace ℝ (Fin 3))
    (a : Fin 2 → EuclideanSpace ℝ (Fin 3))
    (hzero : ∀ i : Fin 2,
      D.coordinateConnectionCoefficient p x u (a i) = 0) :
    tensorCoordinateEvaluation p (D.covariantTensorDerivative T) x
        (Fin.cons u a) =
      fderiv ℝ (fun z => tensorCoordinateEvaluation p T
        ((extChartAt (𝓡 3) p).symm z) a)
        (extChartAt (𝓡 3) p x) u := by
  have h := D.tensorCoordinateDerivative_eq_fderiv_sub hT p hx u a
  have hsum : ∑ i, tensorCoordinateEvaluation p T x
      (Function.update a i (D.coordinateConnectionCoefficient p x u (a i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i]
    obtain ⟨A, hA⟩ := hT.1 x
    simp only [tensorCoordinateEvaluation, hA]
    apply A.map_coord_zero i
    simp [constantCoordinateField]
  rw [hsum, sub_zero] at h
  exact h

end PoincareConjecture.M28.tube
