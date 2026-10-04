import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth

/-!
# All covariant-curvature derivatives under local metric pullbacks

The retained iterated curvature tensors and their metric norms are preserved
by a local isometry. No curvature regularity interface is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

/-- A local isometry transports every slot of every curvature derivative. -/
theorem iteratedCurvature_eq_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (m : ℕ) {x : M} (hx : x ∈ U) (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation m x v =
      D'.iteratedCovariantTensorDerivative D'.riemannEvaluation m (f x)
        (fun i => mfderiv (𝓡 n) (𝓡 n) f x (v i)) := by
  refine D.iteratedCovariantTensorDerivative_eq_pullback D' hU hf hinv hmetric
    D.riemannEvaluation_isSmooth_manifold D'.riemannEvaluation_isSmooth_manifold
    ?_ m hx v
  intro y hy w
  exact D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hy (w 0) (w 1) (w 2) (w 3)

/-- The geometric norms of all covariant-curvature derivatives are unchanged
under a local metric pullback. -/
theorem curvatureDerivativeNorm_eq_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (m : ℕ) {x : M} (hx : x ∈ U) :
    D.curvatureDerivativeNorm m x = D'.curvatureDerivativeNorm m (f x) := by
  obtain ⟨e, he⟩ := hinv x hx
  have he' (v : TangentSpace (𝓡 n) x) : e v = mfderiv (𝓡 n) (𝓡 n) f x v :=
    congrArg (fun L => L v) he
  obtain ⟨A, hA⟩ := (D'.iteratedCovariantTensorDerivative_isSmooth
    D'.riemannEvaluation_isSmooth_manifold m).1 (f x)
  apply g.tensorNorm_eq_of_linearEquiv h _ _ x (f x) e.toLinearEquiv _ _ A hA
  · intro u v
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, he',
      ContinuousLinearEquiv.coe_coe] using (hmetric x hx u v).symm
  · intro v
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, he',
      ContinuousLinearEquiv.coe_coe] using D.iteratedCurvature_eq_pullback D' hU hf hinv hmetric m hx v

end PoincareMT.LeviCivitaData
