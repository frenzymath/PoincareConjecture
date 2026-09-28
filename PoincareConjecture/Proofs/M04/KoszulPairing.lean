import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem metric_derivative_pairing (D : LeviCivitaData g)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) :
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.connection Y x (X x)) (Z x) +
        g.inner x (Y x) (D.connection Z x (X x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ

theorem connection_commutator (D : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) :
    D.connection Y x (X x) - D.connection X x (Y x) =
      VectorField.mlieBracket (𝓡 n) X Y x :=
  D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hX hY

theorem koszul_pairing (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) :
    2 * g.inner x (D.connection Y x (X x)) (Z x) =
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
      g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
      g.inner x (VectorField.mlieBracket (𝓡 n) Y Z x) (X x) +
      g.inner x (VectorField.mlieBracket (𝓡 n) Z X x) (Y x) := by
  have h1 := metric_derivative_pairing D X hY hZ
  have h2 := metric_derivative_pairing D Y hZ hX
  have h3 := metric_derivative_pairing D Z hX hY
  have c1 := congrArg (fun v ↦ g.inner x v (Z x)) (connection_commutator D hX hY)
  have c2 := congrArg (fun v ↦ g.inner x v (X x)) (connection_commutator D hY hZ)
  have c3 := congrArg (fun v ↦ g.inner x v (Y x)) (connection_commutator D hZ hX)
  simp only [map_sub, sub_apply] at c1 c2 c3
  rw [g.symm x (Y x) (D.connection Z x (X x))] at h1
  rw [g.symm x (Z x) (D.connection X x (Y x))] at h2
  rw [g.symm x (X x) (D.connection Y x (Z x))] at h3
  linarith only [h1, h2, h3, c1, c2, c3]

end PoincareConjecture.M04
