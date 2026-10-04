import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.BasisContractions

/-!
# Scalar Hessians and their orthonormal traces

M05 identifies the Hessian with the metric pairing of the gradient's
covariant derivative. M09's generic trace identity then applies to
every orthonormal basis of the actual selected metric.
Morgan-Tian Lemma 6.40 and Proposition 6.43, pp. 126-128.
-/

set_option autoImplicit false
-- The algebraic tangent fibers have the ambient model coordinates before renorming.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Local scalar smoothness gives an actual bilinear Hessian for the
chosen connection, Lemma 6.40, pp. 126-127. -/
theorem hessian_exists_bilinear (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f x) :
    ∃ B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      ∀ v w : TangentSpace (𝓡 n) x, D.hessian f x v w = B v w := by
  refine ⟨(g.inner x).comp (D.connection (D.gradient f) x), ?_⟩
  intro v w
  exact D.hessian_eq_inner_connection_gradient hf v w

/-- The actual selected-slice Laplacian is the Hessian trace in every
orthonormal basis, including in dimension zero, Proposition 6.43, p. 128. -/
theorem laplacian_eq_orthonormal_hessian_trace (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f x)
    {ι : Type*} [Fintype ι] :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x),
      D.laplacian f x = ∑ i, D.hessian f x (b i) (b i) := by
  obtain ⟨H, hH⟩ := hessian_exists_bilinear D f x hf
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ := {
    toFun := fun v => (H v).toLinearMap
    map_add' := by
      intro v w
      ext z
      exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A z) (H.map_add v w)
    map_smul' := by
      intro c v
      ext z
      exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A z) (H.map_smul c v) }
  let B : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    ((LinearMap.toContinuousLinearMap : (TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (TangentSpace (𝓡 n) x →L[ℝ] ℝ)).toLinearMap.comp L).toContinuousLinearMap
  intro b
  have h := Proofs.M09.bilinear_trace_basis_eq B (g.orthonormalBasis x) b
  change (∑ i, H (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
    ∑ i, H (b i) (b i) at h
  change (∑ i, D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = _
  exact (Finset.sum_congr rfl (fun i _ => hH _ _)).trans
    (h.trans (Finset.sum_congr rfl (fun i _ => (hH _ _).symm)))

end PoincareMT.M14
