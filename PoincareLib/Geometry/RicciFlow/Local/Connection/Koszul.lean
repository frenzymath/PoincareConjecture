/- Adapted from Mapher `PoincareMT/Proofs/Ch01/Koszul.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.Riemannian.Connection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local Koszul formula and uniqueness on regular sections

The formula follows from the metric-compatibility and torsion identities in
Morgan-Tian, Theorem 1.2, printed pp. 3-4. These results require differentiability
only at the evaluation point. They do not assert existence or equality of
connection operators on arbitrary nondifferentiable sections.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Metric compatibility with the specified metric visible in the scalar derivative. -/
theorem localTheory_mvfderiv_inner (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.connection Y x (X x)) (Z x) +
        g.inner x (Y x) (D.connection Z x (X x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ

/-- The Koszul formula on vector fields differentiable at the evaluation point. -/
theorem koszul (D : LeviCivitaData g)
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
  rw [D.localTheory_mvfderiv_inner X Y Z hY hZ, D.localTheory_mvfderiv_inner Y Z X hZ hX,
    D.localTheory_mvfderiv_inner Z X Y hX hY]
  rw [← (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hX hY,
    ← (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hX hZ,
    ← (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) hY hZ]
  simp only [map_sub, sub_apply]
  rw [g.symm x (D.connection Z x (Y x)) (X x),
    g.symm x (Z x) (D.connection X x (Y x)),
    g.symm x (D.connection X x (Z x)) (Y x)]
  ring

/-- Compatible torsion-free connections agree on a section differentiable at a point. -/
theorem connection_eq_at (D D' : LeviCivitaData g)
    (Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.connection Y x = D'.connection Y x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ext u
  apply ext_inner_right ℝ
  intro v
  change g.inner x (D.connection Y x u) v = g.inner x (D'.connection Y x u) v
  have hD := D.koszul (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u) Y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.mdifferentiableAt_extend ..) hY (FiberBundle.mdifferentiableAt_extend ..)
  have hD' := D'.koszul (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u) Y
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.mdifferentiableAt_extend ..) hY (FiberBundle.mdifferentiableAt_extend ..)
  simp only [FiberBundle.extend_apply_self] at hD hD'
  linarith only [hD, hD']

end PoincareMT.LeviCivitaData
