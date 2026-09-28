import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem leviCivita_koszul_at {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (x : M) (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Z) x) :
    2 * g.inner x (D.connection Y x (X x)) (Z x) =
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Z y)) x (Y x) -
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
      g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
      g.inner x (VectorField.mlieBracket (𝓡 n) Y Z x) (X x) -
      g.inner x (VectorField.mlieBracket (𝓡 n) X Z x) (Y x) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hA : mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.connection Y x (X x)) (Z x) +
        g.inner x (Y x) (D.connection Z x (X x)) :=
    D.metricCompatible.mvfderiv_inner_eq X hY hZ
  have hB : mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Z y)) x (Y x) =
      g.inner x (D.connection X x (Y x)) (Z x) +
        g.inner x (X x) (D.connection Z x (Y x)) :=
    D.metricCompatible.mvfderiv_inner_eq Y hX hZ
  have hC : mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) =
      g.inner x (D.connection X x (Z x)) (Y x) +
        g.inner x (X x) (D.connection Y x (Z x)) :=
    D.metricCompatible.mvfderiv_inner_eq Z hX hY
  have hXY := congrArg (fun v ↦ g.inner x v (Z x))
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hX hY)
  have hYZ := congrArg (fun v ↦ g.inner x v (X x))
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hY hZ)
  have hXZ := congrArg (fun v ↦ g.inner x v (Y x))
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hX hZ)
  simp only [map_sub, ContinuousLinearMap.sub_apply] at hXY hYZ hXZ
  rw [g.symm x (Y x) (D.connection Z x (X x))] at hA
  rw [g.symm x (X x) (D.connection Z x (Y x))] at hB
  rw [g.symm x (X x) (D.connection Y x (Z x))] at hC
  linarith

end PoincareConjecture.Proofs.M09
