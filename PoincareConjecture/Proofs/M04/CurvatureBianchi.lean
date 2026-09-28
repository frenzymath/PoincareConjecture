import PoincareConjecture.Proofs.M04.CurvatureAlgebra
import PoincareConjecture.Proofs.M04.ConnectionScalar
import PoincareConjecture.Proofs.M04.MetricPairings
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_cyclic (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x + D.curvatureOnFields Y Z X x +
      D.curvatureOnFields Z X Y x = 0 := by
  let V : Fin 3 → (y : M) → TangentSpace (𝓡 n) y := ![X, Y, Z]
  have hV (i : Fin 3) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (V i)) U := by
    fin_cases i
    · exact hX
    · exact hY
    · exact hZ
  let A (i j : Fin 3) := fun y ↦ D.connection (V j) y (V i y)
  have hA (i j : Fin 3) (_hij : i ≠ j) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (A i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (A i j)
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hy' : y ∈ U ∩ t.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      ((hV i).mono Set.inter_subset_left) ((hV j).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hy')
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (by
          exact WithTop.coe_le_coe.mpr
            (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (by
          exact WithTop.coe_le_coe.mpr
            (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  have hVAt (i : Fin 3) := ((hV i) x hx).contMDiffAt (hU.mem_nhds hx)
  have hVD (i : Fin 3) := (hVAt i).mdifferentiableAt (by simp)
  have hAD (i j : Fin 3) (hij : i ≠ j) :=
    (((hA i j hij) x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hBD (i j : Fin 3) :=
    ((hVAt i).mlieBracket_vectorField (m := ⊤) (n := ⊤) (hVAt j)
      (by simp)).mdifferentiableAt (by simp)
  have hT (i j : Fin 3) : ∀ y ∈ U,
      A i j y - A j i y = VectorField.mlieBracket (𝓡 n) (V i) (V j) y := by
    intro y hy
    exact connection_commutator D
      (((hV i) y hy).contMDiffAt (hU.mem_nhds hy) |>.mdifferentiableAt (by simp))
      (((hV j) y hy).contMDiffAt (hU.mem_nhds hy) |>.mdifferentiableAt (by simp))
  have hDA (i j k : Fin 3) (hij : i ≠ j) :
      D.connection (VectorField.mlieBracket (𝓡 n) (V i) (V j)) x (V k x) =
        D.connection (A i j) x (V k x) - D.connection (A j i) x (V k x) := by
    have heq := (D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
      (mdifferentiableAt_sub_section (hAD i j hij) (hAD j i (Ne.symm hij)))
      (hBD i j) (hU.mem_nhds hx) (hT i j)
    rw [← heq]
    have hn : D.connection (-(A j i)) x = -D.connection (A j i) x := by
      simpa only [neg_one_smul] using
        D.connection.isCovariantDerivativeOnUniv.smul_const (-1 : ℝ) (hAD j i (Ne.symm hij))
    have ha := D.connection.isCovariantDerivativeOnUniv.add
      (hAD i j hij) (mdifferentiableAt_neg_section (hAD j i (Ne.symm hij)))
    rw [hn] at ha
    simpa only [sub_eq_add_neg, add_apply, neg_apply] using
      congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x ↦ L (V k x)) ha
  have h1 := connection_commutator D (hVD 0) (hBD 1 2)
  have h2 := connection_commutator D (hVD 1) (hBD 2 0)
  have h3 := connection_commutator D (hVD 2) (hBD 0 1)
  rw [hDA 1 2 0 (by decide)] at h1
  rw [hDA 2 0 1 (by decide)] at h2
  rw [hDA 0 1 2 (by decide)] at h3
  have hsum :
      D.curvatureOnFields (V 0) (V 1) (V 2) x +
        D.curvatureOnFields (V 1) (V 2) (V 0) x +
        D.curvatureOnFields (V 2) (V 0) (V 1) x =
      VectorField.mlieBracket (𝓡 n) (V 0) (VectorField.mlieBracket (𝓡 n) (V 1) (V 2)) x +
        VectorField.mlieBracket (𝓡 n) (V 1) (VectorField.mlieBracket (𝓡 n) (V 2) (V 0)) x +
        VectorField.mlieBracket (𝓡 n) (V 2) (VectorField.mlieBracket (𝓡 n) (V 0) (V 1)) x := by
    rw [← h1, ← h2, ← h3]
    simp only [LeviCivitaData.curvatureOnFields, A]
    abel
  have hmin : (minSmoothness ℝ 2 : ℕ∞ω) ≤ ∞ := by
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (by
          exact WithTop.coe_le_coe.mpr
            (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  have hJ := VectorField.leibniz_identity_mlieBracket_apply
    ((hVAt 0).of_le hmin) ((hVAt 1).of_le hmin) ((hVAt 2).of_le hmin)
  rw [VectorField.mlieBracket_swap_apply
    (V := VectorField.mlieBracket (𝓡 n) (V 0) (V 1)) (W := V 2)] at hJ
  rw [VectorField.mlieBracket_swap (V := V 0) (W := V 2)] at hJ
  have hn : VectorField.mlieBracket (𝓡 n) (V 1)
      (-VectorField.mlieBracket (𝓡 n) (V 2) (V 0)) x =
      -VectorField.mlieBracket (𝓡 n) (V 1)
        (VectorField.mlieBracket (𝓡 n) (V 2) (V 0)) x := by
    simpa only [neg_one_smul] using
      (VectorField.mlieBracket_const_smul_right (V := V 1) (c := (-1 : ℝ)) (hBD 2 0))
  rw [hn] at hJ
  change D.curvatureOnFields (V 0) (V 1) (V 2) x +
    D.curvatureOnFields (V 1) (V 2) (V 0) x + D.curvatureOnFields (V 2) (V 0) (V 1) x = 0
  rw [hsum, hJ]
  abel

theorem curvature_cyclic (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w + D.curvature x v w u + D.curvature x w u v = 0 := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  exact curvatureOnFields_cyclic D t.open_baseSet
    (contMDiffOn_extend_baseSet u) (contMDiffOn_extend_baseSet v)
    (contMDiffOn_extend_baseSet w) (FiberBundle.mem_baseSet_trivializationAt' x)

end PoincareConjecture.M04
