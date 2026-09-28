import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import PoincareConjecture.Proofs.M07.Geometry.Manifold.VectorField.Commutator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem normalization_mvfderiv_inner (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.connection Y x (X x)) (Z x) +
        g.inner x (Y x) (D.connection Z x (X x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ

theorem normalization_koszul (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    2 * g.inner x (D.connection Y x (X x)) (Z x) =
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
      g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
      g.inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
      g.inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x) := by
  rw [D.normalization_mvfderiv_inner X Y Z hY hZ, D.normalization_mvfderiv_inner Y Z X hZ hX,
    D.normalization_mvfderiv_inner Z X Y hX hY]
  rw [← (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hX hY,
    ← (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hX hZ,
    ← (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hY hZ]
  simp only [map_sub, sub_apply]
  rw [g.symm x (D.connection Z x (Y x)) (X x),
    g.symm x (Z x) (D.connection X x (Y x)),
    g.symm x (D.connection X x (Z x)) (Y x)]
  ring

theorem normalization_connection_eq_at (D D' : LeviCivitaData g)
    (Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.connection Y x = D'.connection Y x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ext u
  apply ext_inner_right ℝ
  intro v
  change g.inner x (D.connection Y x u) v = g.inner x (D'.connection Y x u) v
  have hD := D.normalization_koszul (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u) Y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.mdifferentiableAt_extend ..) hY (FiberBundle.mdifferentiableAt_extend ..)
  have hD' := D'.normalization_koszul (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u) Y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.mdifferentiableAt_extend ..) hY (FiberBundle.mdifferentiableAt_extend ..)
  simp only [FiberBundle.extend_apply_self] at hD hD'
  linarith only [hD, hD']

end PoincareConjecture.LeviCivitaData
