import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Matrix

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))

theorem pullbackVolumeDensity_id_bounds (x : EuclideanSpace ℝ (Fin n))
    {a b : ℝ} (ha : 0 < a)
    (hell : ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) :
    Real.sqrt (a ^ n) ≤ g.pullbackVolumeDensity id x ∧
      g.pullbackVolumeDensity id x ≤ Real.sqrt (b ^ n) := by
  classical
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let B := (g.euclideanCoefficients x).toBilinForm
  let G := LinearMap.BilinForm.toMatrix e B
  have hG : G.IsHermitian := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.conjTranspose_apply, G, LinearMap.BilinForm.toMatrix_apply,
      star_trivial]
    exact g.symm x (e j) (e i)
  have hrepr (v : EuclideanSpace ℝ (Fin n)) : ⇑(e.repr v) = WithLp.ofLp v := by
    funext i
    simp [e, OrthonormalBasis.coe_toBasis_repr_apply]
  have hform (u v : EuclideanSpace ℝ (Fin n)) :
      g.euclideanCoefficients x u v =
        (WithLp.ofLp u) ⬝ᵥ G *ᵥ (WithLp.ofLp v) := by
    simpa only [hrepr, B, G] using!
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e B u v
  have heigen (i : Fin n) :
      hG.eigenvalues i = g.euclideanCoefficients x
        (hG.eigenvectorBasis i) (hG.eigenvectorBasis i) := by
    rw [hG.eigenvalues_eq, hform]
    simp
  have heigen_bounds (i : Fin n) :
      a ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ b := by
    simpa [← heigen, hG.eigenvectorBasis.orthonormal.1 i] using
      hell (hG.eigenvectorBasis i)
  have hdet_lower : a ^ n ≤ G.det := by
    rw [hG.det_eq_prod_eigenvalues]
    have h := Finset.prod_le_prod (s := Finset.univ)
      (f := fun _ : Fin n => a) (g := hG.eigenvalues)
      (fun _ _ => ha.le) (fun i _ => (heigen_bounds i).1)
    simpa using h
  have hdet_upper : G.det ≤ b ^ n := by
    rw [hG.det_eq_prod_eigenvalues]
    have h := Finset.prod_le_prod (s := Finset.univ)
      (f := hG.eigenvalues) (g := fun _ : Fin n => b)
      (fun i _ => ha.le.trans (heigen_bounds i).1)
      (fun i _ => (heigen_bounds i).2)
    simpa using h
  have hdensity : g.pullbackVolumeDensity id x = Real.sqrt G.det := by
    unfold pullbackVolumeDensity
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply, Matrix.of_apply,
      G, LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [hdensity]
  exact ⟨Real.sqrt_le_sqrt hdet_lower, Real.sqrt_le_sqrt hdet_upper⟩

end PoincareConjecture.RiemannianMetric
