import PoincareConjecture.Definitions.Ch01.Curvature
import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def MetricComplete (g : RiemannianMetric n M) [T3Space M] : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  CompleteSpace M

namespace LeviCivitaData

def IsSkewCoefficient (d : ℕ) (A : Fin d → Fin d → ℝ) : Prop :=
  ∀ i j, A i j = -A j i

noncomputable def curvatureOperatorQuadratic (D : LeviCivitaData g)
    (x : M) (A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, ∑ k, ∑ l,
    A i j * A k l * D.curvatureTensor x (b i) (b j) (b k) (b l)

def NonnegativeCurvatureOperator (D : LeviCivitaData g)
    (x : M) : Prop :=
  ∀ A, IsSkewCoefficient (Module.finrank ℝ (TangentSpace (𝓡 n) x)) A →
    0 ≤ D.curvatureOperatorQuadratic x A

def CurvatureOperatorBound (D : LeviCivitaData g)
    (K : ℝ) (x : M) : Prop :=
  ∀ A, IsSkewCoefficient (Module.finrank ℝ (TangentSpace (𝓡 n) x)) A →
    |D.curvatureOperatorQuadratic x A| ≤
      K * ∑ i, ∑ j, (A i j) ^ 2

end LeviCivitaData

noncomputable def spacetimeEnergy {J : Set ℝ} (F : RicciFlow n M J)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ s in a..b,
    (F.metric s).inner (γ s)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)

end PoincareConjecture
