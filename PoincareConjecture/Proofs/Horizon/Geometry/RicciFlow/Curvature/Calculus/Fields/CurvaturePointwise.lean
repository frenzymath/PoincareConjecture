import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.CurvatureFieldLinearity
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology

universe u v

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_sum_left (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {α : Type v} (s : Finset α)
    {X : α → (x : M) → TangentSpace (𝓡 n) x}
    {Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ∀ i ∈ s, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields (fun y ↦ ∑ i ∈ s, X i y) Y Z x =
      ∑ i ∈ s, D.curvatureOnFields (X i) Y Z x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.smul_def', zero_smul] using!
      curvatureOnFields_smul_left D hU
      (f := fun _ ↦ (0 : ℝ)) contMDiffOn_const hY hY hZ hx
  | insert i s hi ih =>
    have hXs (j : α) (hj : j ∈ s) := hX j (Finset.mem_insert_of_mem hj)
    have hS := ContMDiffOn.sum_section hXs
    have ha := curvatureOnFields_add_left D hU
      (hX i (Finset.mem_insert_self i s)) hS hY hZ hx
    rw [ih hXs] at ha
    simpa only [Finset.sum_insert hi, Pi.add_def] using! ha

theorem curvatureOnFields_sum_third (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {α : Type v} (s : Finset α)
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    {Z : α → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ∀ i ∈ s, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (Z i)) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y (fun y ↦ ∑ i ∈ s, Z i y) x =
      ∑ i ∈ s, D.curvatureOnFields X Y (Z i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.smul_def', zero_smul] using!
      curvatureOnFields_smul_third D hU
      (f := fun _ ↦ (0 : ℝ)) contMDiffOn_const hX hY hX hx
  | insert i s hi ih =>
    have hZs (j : α) (hj : j ∈ s) := hZ j (Finset.mem_insert_of_mem hj)
    have hS := ContMDiffOn.sum_section hZs
    have ha := curvatureOnFields_add_third D hU hX hY
      (hZ i (Finset.mem_insert_self i s)) hS hx
    rw [ih hZs] at ha
    simpa only [Finset.sum_insert hi, Pi.add_def] using! ha

theorem curvatureOnFields_congr_left_at (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X X' Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hX' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X') U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) (he : X x = X' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y Z x := by
  classical
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let E := t.localFrame b
  let V : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![X, X']
  have hV (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (V i)) O := by
    fin_cases i
    · exact hX.mono Set.inter_subset_left
    · exact hX'.mono Set.inter_subset_left
  have hE (j : Fin n) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (E j)) O :=
    (t.contMDiffOn_localFrame_baseSet (n := ∞) b j).mono Set.inter_subset_right
  have hYO := hY.mono (t := O) Set.inter_subset_left
  have hZO := hZ.mono (t := O) Set.inter_subset_left
  let C (i : Fin 2) (j : Fin n) := fun y ↦ t.localFrameCoeff (𝓡 n) b j y (V i y)
  have hC (i : Fin 2) (j : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C i j) O :=
    contMDiffOn_localFrameCoeff b hO Set.inter_subset_right (hV i) j
  have hSum (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (fun y ↦ ∑ j, C i j y • E j y)) O :=
    ContMDiffOn.sum_section fun j _ ↦ (hC i j).smul_section (hE j)
  have hR (i : Fin 2) : D.curvatureOnFields (V i) Y Z x =
      ∑ j, C i j x • D.curvatureOnFields (E j) Y Z x := by
    calc
      _ = D.curvatureOnFields (fun y ↦ ∑ j, C i j y • E j y) Y Z x := by
        apply curvatureOnFields_congr D hO (hV i) hYO hZO (hSum i) hYO hZO
          ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hxO
        intro y hy
        exact t.eq_sum_localFrameCoeff_smul (b := b) hy.2
      _ = ∑ j, D.curvatureOnFields (fun y ↦ C i j y • E j y) Y Z x :=
        curvatureOnFields_sum_left D hO Finset.univ
          (fun j _ ↦ (hC i j).smul_section (hE j)) hYO hZO hxO
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact curvatureOnFields_smul_left D hO (hC i j) (hE j) hYO hZO hxO
  change D.curvatureOnFields (V 0) Y Z x = D.curvatureOnFields (V 1) Y Z x
  rw [hR 0, hR 1]
  apply Finset.sum_congr rfl
  intro j _
  change t.localFrameCoeff (𝓡 n) b j x (X x) • _ =
    t.localFrameCoeff (𝓡 n) b j x (X' x) • _
  rw [he]

theorem curvatureOnFields_congr_third_at (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z Z' : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z') U) {x : M} (hx : x ∈ U) (he : Z x = Z' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X Y Z' x := by
  classical
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let E := t.localFrame b
  let V : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![Z, Z']
  have hV (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (V i)) O := by
    fin_cases i
    · exact hZ.mono Set.inter_subset_left
    · exact hZ'.mono Set.inter_subset_left
  have hE (j : Fin n) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (E j)) O :=
    (t.contMDiffOn_localFrame_baseSet (n := ∞) b j).mono Set.inter_subset_right
  have hXO := hX.mono (t := O) Set.inter_subset_left
  have hYO := hY.mono (t := O) Set.inter_subset_left
  let C (i : Fin 2) (j : Fin n) := fun y ↦ t.localFrameCoeff (𝓡 n) b j y (V i y)
  have hC (i : Fin 2) (j : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C i j) O :=
    contMDiffOn_localFrameCoeff b hO Set.inter_subset_right (hV i) j
  have hSum (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (fun y ↦ ∑ j, C i j y • E j y)) O :=
    ContMDiffOn.sum_section fun j _ ↦ (hC i j).smul_section (hE j)
  have hR (i : Fin 2) : D.curvatureOnFields X Y (V i) x =
      ∑ j, C i j x • D.curvatureOnFields X Y (E j) x := by
    calc
      _ = D.curvatureOnFields X Y (fun y ↦ ∑ j, C i j y • E j y) x := by
        apply curvatureOnFields_congr D hO hXO hYO (hV i) hXO hYO (hSum i)
          (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ?_ hxO
        intro y hy
        exact t.eq_sum_localFrameCoeff_smul (b := b) hy.2
      _ = ∑ j, D.curvatureOnFields X Y (fun y ↦ C i j y • E j y) x :=
        curvatureOnFields_sum_third D hO Finset.univ hXO hYO
          (fun j _ ↦ (hC i j).smul_section (hE j)) hxO
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact curvatureOnFields_smul_third D hO (hC i j) hXO hYO (hE j) hxO
  change D.curvatureOnFields X Y (V 0) x = D.curvatureOnFields X Y (V 1) x
  rw [hR 0, hR 1]
  apply Finset.sum_congr rfl
  intro j _
  change t.localFrameCoeff (𝓡 n) b j x (Z x) • _ =
    t.localFrameCoeff (𝓡 n) b j x (Z' x) • _
  rw [he]

theorem curvatureOnFields_eq_curvature (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x = D.curvature x (X x) (Y x) (Z x) := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hXO := hX.mono (t := O) Set.inter_subset_left
  have hYO := hY.mono (t := O) Set.inter_subset_left
  have hZO := hZ.mono (t := O) Set.inter_subset_left
  let A := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (X x)
  let B := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x)
  let C := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Z x)
  have hA := (contMDiffOn_extend_baseSet (X x)).mono (t := O) Set.inter_subset_right
  have hB := (contMDiffOn_extend_baseSet (Y x)).mono (t := O) Set.inter_subset_right
  have hC := (contMDiffOn_extend_baseSet (Z x)).mono (t := O) Set.inter_subset_right
  calc
    _ = D.curvatureOnFields A Y Z x :=
      curvatureOnFields_congr_left_at D hO hXO hA hYO hZO hxO
        (FiberBundle.extend_apply_self _ _).symm
    _ = -D.curvatureOnFields Y A Z x := curvatureOnFields_swap D Y A Z x
    _ = -D.curvatureOnFields B A Z x := congrArg Neg.neg
      (curvatureOnFields_congr_left_at D hO hYO hB hA hZO hxO
        (FiberBundle.extend_apply_self _ _).symm)
    _ = D.curvatureOnFields A B Z x := by rw [curvatureOnFields_swap D A B Z x, neg_neg]
    _ = D.curvatureOnFields A B C x :=
      curvatureOnFields_congr_third_at D hO hA hB hZO hC hxO
        (FiberBundle.extend_apply_self _ _).symm
    _ = _ := rfl

end PoincareConjecture.RicciFlowAnalysis
