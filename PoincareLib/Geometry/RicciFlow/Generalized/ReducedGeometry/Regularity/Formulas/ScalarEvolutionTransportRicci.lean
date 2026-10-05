import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.FrameForms
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.BasisContractions
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.CurvatureCalculus
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareLib.Geometry.Riemannian.ScalarOperators

/-!
# Ricci norm transport for generalized scalar evolution

The actual full Ricci contraction is independent of the selected
orthonormal basis and is preserved by the slice local isometry.
This supplies the quadratic term in Morgan-Tian Theorem 3.13,
equation (3.7), p. 41, as used in Section 6.5, pp. 126-127.
-/

set_option autoImplicit false
-- The transported orthonormal bases use the selected metric fiber instances.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M14

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

/-- The retained Ricci norm is the full squared contraction in any
metric orthonormal basis, Theorem 3.13, equation (3.7), p. 41. -/
theorem ricciNormSq_eq_orthonormal_sum (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ e : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x),
      D.ricciNormSq x = ∑ i, ∑ j, (D.ricci x (e i) (e j)) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro e
  have hb := Proofs.M09.bilinear_square_basis_eq
    (Proofs.M09.tensorBilinear g D.ricciEvaluation
      D.normalization_curvatureTensorCalculus.2.1 x) (g.orthonormalBasis x) e
  simpa only [Proofs.M09.tensorBilinear_apply, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, LeviCivitaData.ricciNormSq] using hb

/-- The actual Ricci squared norm is preserved by a smooth local
isometry, Theorem 3.13, equation (3.7), p. 41, and Definition 3.38, p. 61. -/
theorem ricciNormSq_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    {x : M} (hx : x ∈ U) : D.ricciNormSq x = D'.ricciNormSq (f x) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  rw [ricciNormSq_eq_orthonormal_sum D' (f x) ((g.orthonormalBasis x).map e')]
  change (∑ i, ∑ j, (D.ricci x (g.orthonormalBasis x i)
      (g.orthonormalBasis x j)) ^ 2) =
    ∑ i, ∑ j, (D'.ricci (f x) (e (g.orthonormalBasis x i))
      (e (g.orthonormalBasis x j))) ^ 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun r : ℝ => r ^ 2)
    (D.ricci_eq_of_local_isometry D' hU hf hmetric hx _ _)

end PoincareMT.M14
