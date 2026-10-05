import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceScalarEstimates
import PoincareLib.Geometry.Riemannian.Homothety.Curvature.ContractionTransport
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Pullback

/-!
# The scalar evolution term on an actual ordinary slice

Morgan-Tian Theorem 12.28, pp. 323-324, and Lemma 11.2, p. 270.
The slice isometry transports both the scalar Laplacian and the full
Ricci squared norm, hence the absolute evolution bound in a cap certificate.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.28: the actual retained Ricci squared norm is unchanged
under the valid-slice isometry, independently of the chosen bases. -/
theorem ricciNormSq_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (connection F t).ricciNormSq ((sliceDiffeomorph ht).symm x) =
      (F.connection t).ricciNormSq x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (slice J t).carrier → Type _) :=
    ⟨(metric F t).toRiemannianMetric⟩
  let f := (sliceDiffeomorph ht).symm
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : (slice J t).carrier → Type _) (f x)
  let b := (F.metric t).orthonormalBasis x
  let e := M13.homothetyTangentIsometry (F.metric t) (metric F t) f 1 zero_lt_one
    (slice_homothety F ht) x
  have he (v : TangentSpace (𝓡 3) x) : e v = mfderiv (𝓡 3) (𝓡 3) f x v := by
    simp only [e, M13.homothetyTangentIsometry_apply, Real.sqrt_one, inv_one, one_smul]
  calc
    _ = ∑ i, ∑ j, ((connection F t).ricci (f x) (e (b i)) (e (b j))) ^ 2 :=
      M13.sum_sq_bilinear_basis_eq (M13.ricciLinear (connection F t) (f x))
        ((metric F t).orthonormalBasis (f x)) (b.map e)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [he, he]
      exact congrArg (fun r : ℝ => r ^ 2)
        ((slice_calculus P F ht).ricci_eq (F.connection t) (connection F t) x (b i) (b j))

/-- Theorem 12.28: the actual scalar evolution expression agrees on
the retained slice and on the original ordinary flow at every valid time. -/
theorem scalar_evolution_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (connection F t).laplacian (connection F t).scalarCurvature
        ((sliceDiffeomorph ht).symm x) +
        2 * (connection F t).ricciNormSq ((sliceDiffeomorph ht).symm x) =
      (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x := by
  have hscalar : (connection F t).scalarCurvature =
      (F.connection t).scalarCurvature ∘ (sliceDiffeomorph ht) := by
    funext y
    exact scalar_eq P F ht y.val
  have hreg := Poincare.RicciFlow.Harnack.scalarCurvature_contMDiff_slice P.curvature J F t ht
  have hlap := (connection F t).laplacian_comp_of_metric_pullback (F.connection t)
    (f := sliceDiffeomorph ht) (x := (sliceDiffeomorph ht).symm x)
    (sliceDiffeomorph ht).contMDiffAt
    (Eventually.of_forall (M13.diffeomorph_mfderiv_isInvertible (sliceDiffeomorph ht)))
    (Eventually.of_forall (fun _ _ _ => rfl)) hreg.contMDiffAt
  exact congrArg₂ (fun a b : ℝ => a + 2 * b)
    ((congrArg (fun f => (connection F t).laplacian f
      ((sliceDiffeomorph ht).symm x)) hscalar).trans hlap)
    (ricciNormSq_eq P F ht x)

end PoincareMT.M35.OrdinaryRealization
