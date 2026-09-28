import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module


















set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma horizon_mvfderiv_inner (D : LeviCivitaData g)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.covariantDerivativeOnFields X Y x) (Z x) +
      g.inner x (Y x) (D.covariantDerivativeOnFields X Z x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ

end PoincareConjecture.LeviCivitaData
