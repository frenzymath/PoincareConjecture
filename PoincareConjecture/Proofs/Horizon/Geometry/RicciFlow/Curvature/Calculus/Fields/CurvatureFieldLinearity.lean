import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import Mathlib.Tactic.Module









set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_congr (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    {X Y Z X' Y' Z' : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U)
    (hX' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X') U)
    (hY' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y') U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z') U)
    (heX : ∀ y ∈ U, X y = X' y) (heY : ∀ y ∈ U, Y y = Y' y)
    (heZ : ∀ y ∈ U, Z y = Z' y) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y' Z' x := by
  let V : Fin 2 → Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![![X, Y], ![X', Y']]
  let S : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![Z, Z']
  have hV (j i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (V j i)) U := by
    fin_cases j <;> fin_cases i
    · exact hX
    · exact hY
    · exact hX'
    · exact hY'
  have hS (j : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (S j)) U := by
    fin_cases j
    · exact hZ
    · exact hZ'
  let A (j i : Fin 2) := fun y ↦ D.connection (S j) y (V j i y)
  have hA (j i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (A j i)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (A j i)
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hy' : y ∈ U ∩ t.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      ((hV j i).mono Set.inter_subset_left) ((hS j).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hy')
  have hDZ {y : M} (hy : y ∈ U) : D.connection Z y = D.connection Z' y :=
    (D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
      ((hZ y hy).contMDiffAt (hU.mem_nhds hy) |>.mdifferentiableAt (by simp))
      ((hZ' y hy).contMDiffAt (hU.mem_nhds hy) |>.mdifferentiableAt (by simp))
      (hU.mem_nhds hy) heZ
  have heA (i : Fin 2) : ∀ y ∈ U, A 0 i y = A 1 i y := by
    intro y hy
    fin_cases i
    · change D.connection Z y (X y) = D.connection Z' y (X' y)
      rw [hDZ hy, heX y hy]
    · change D.connection Z y (Y y) = D.connection Z' y (Y' y)
      rw [hDZ hy, heY y hy]
  have hDA (i : Fin 2) : D.connection (A 0 i) x = D.connection (A 1 i) x :=
    (D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
      (((hA 0 i) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
      (((hA 1 i) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
      (hU.mem_nhds hx) (heA i)
  have heX' : X =ᶠ[𝓝 x] X' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heX
  have heY' : Y =ᶠ[𝓝 x] Y' := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heY
  have hB := heX'.mlieBracket_vectorField_eq (I := 𝓡 n) heY'
  change D.connection (A 0 1) x (X x) - D.connection (A 0 0) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x) =
    D.connection (A 1 1) x (X' x) - D.connection (A 1 0) x (Y' x) -
      D.connection Z' x (VectorField.mlieBracket (𝓡 n) X' Y' x)
  rw [hDA 1, hDA 0, heX x hx, heY x hx, hDZ hx, hB]

theorem curvatureOnFields_add_left (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X X' Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hX' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X') U)
    (_hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields (X + X') Y Z x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X' Y Z x := by
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  let V : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![X, X']
  have hV (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (V i)) U := by
    fin_cases i
    · exact hX
    · exact hX'
  let A (i : Fin 2) := fun y ↦ D.connection Z y (V i y)
  have hA (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (A i)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (A i)
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hy' : y ∈ U ∩ t.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      ((hV i).mono Set.inter_subset_left) (hZ.mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hy')
  have hAD (i : Fin 2) :=
    (((hA i) x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have he : (fun y ↦ D.connection Z y ((X + X') y)) = A 0 + A 1 := by
    funext y
    exact map_add (D.connection Z y) (X y) (X' y)
  have hB := VectorField.mlieBracket_add_left (W := Y)
    ((hX x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
    ((hX' x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
  simp only [LeviCivitaData.curvatureOnFields]
  rw [he, D.connection.isCovariantDerivativeOnUniv.add (hAD 0) (hAD 1), hB]
  simp only [Pi.add_apply, map_add, add_apply, A, V, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  abel

theorem curvatureOnFields_smul_left (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (_hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields (f • X) Y Z x = f x • D.curvatureOnFields X Y Z x := by
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  let A := fun y ↦ D.connection Z y (X y)
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g A
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hy' : y ∈ U ∩ t.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      (hX.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hy')
  have hAD := ((hA x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hfD := ((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have he : (fun y ↦ D.connection Z y ((f • X) y)) = f • A := by
    funext y
    exact map_smul (D.connection Z y) (f y) (X y)
  have hB := VectorField.mlieBracket_smul_left (W := Y) hfD
    ((hX x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
  simp only [LeviCivitaData.curvatureOnFields]
  rw [he, D.connection.isCovariantDerivativeOnUniv.leibniz hAD hfD, hB]
  simp only [Pi.smul_apply', map_add, map_smul, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, A]
  module

theorem curvatureOnFields_add_third (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z Z' : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z') U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y (Z + Z') x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y Z' x := by
  let a := D.curvatureOnFields X Y (Z + Z') x -
    (D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y Z' x)
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hx' : x ∈ U ∩ t.baseSet := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hX' := hX.mono (t := U ∩ t.baseSet) Set.inter_subset_left
  have hY' := hY.mono (t := U ∩ t.baseSet) Set.inter_subset_left
  have hW := (contMDiffOn_extend_baseSet a).mono (t := U ∩ t.baseSet) Set.inter_subset_right
  have h0 := curvatureOnFields_metric_skew D (hU.inter t.open_baseSet)
    hX' hY' ((hZ.add_section hZ').mono Set.inter_subset_left) hW hx'
  have h1 := curvatureOnFields_metric_skew D (hU.inter t.open_baseSet)
    hX' hY' (hZ.mono Set.inter_subset_left) hW hx'
  have h2 := curvatureOnFields_metric_skew D (hU.inter t.open_baseSet)
    hX' hY' (hZ'.mono Set.inter_subset_left) hW hx'
  simp only [FiberBundle.extend_apply_self, Pi.add_apply, map_add] at h0 h1 h2
  have hz : g.inner x a a = 0 := by
    change g.inner x (D.curvatureOnFields X Y (Z + Z') x -
      (D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y Z' x)) a = 0
    simp only [map_sub, sub_apply, map_add, add_apply]
    linarith only [h0, h1, h2]
  apply sub_eq_zero.mp
  by_contra hne
  exact (ne_of_gt (g.pos x a hne)) hz

theorem curvatureOnFields_smul_third (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y (f • Z) x = f x • D.curvatureOnFields X Y Z x := by
  let a := D.curvatureOnFields X Y (f • Z) x - f x • D.curvatureOnFields X Y Z x
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hx' : x ∈ U ∩ t.baseSet := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hX' := hX.mono (t := U ∩ t.baseSet) Set.inter_subset_left
  have hY' := hY.mono (t := U ∩ t.baseSet) Set.inter_subset_left
  have hW := (contMDiffOn_extend_baseSet a).mono (t := U ∩ t.baseSet) Set.inter_subset_right
  have h0 := curvatureOnFields_metric_skew D (hU.inter t.open_baseSet)
    hX' hY' ((hf.smul_section hZ).mono Set.inter_subset_left) hW hx'
  have h1 := curvatureOnFields_metric_skew D (hU.inter t.open_baseSet)
    hX' hY' (hZ.mono Set.inter_subset_left) hW hx'
  simp only [FiberBundle.extend_apply_self, Pi.smul_apply', map_smul, smul_eq_mul] at h0 h1
  have hz : g.inner x a a = 0 := by
    change g.inner x (D.curvatureOnFields X Y (f • Z) x -
      f x • D.curvatureOnFields X Y Z x) a = 0
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
    rw [h0, h1]
    ring
  apply sub_eq_zero.mp
  by_contra hne
  exact (ne_of_gt (g.pos x a hne)) hz

end PoincareConjecture.RicciFlowAnalysis
