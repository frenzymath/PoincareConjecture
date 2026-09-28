import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeFields
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem covariantTensorDerivativeOnFields_congr_at (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {X Y : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U)
    (hY : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (Y i)) U) {x : M} (hx : x ∈ U) (hXY : ∀ i, X i x = Y i x) :
    covariantTensorDerivativeOnFields D T X x =
      covariantTensorDerivativeOnFields D T Y x := by
  classical
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  have hOne (Z : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (Z j)) U) (i : Fin (k + 1))
      (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% B) U) (he : A x = B x) :
      covariantTensorDerivativeOnFields D T (Function.update Z i A) x =
        covariantTensorDerivativeOnFields D T (Function.update Z i B) x := by
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let O := U ∩ t.baseSet
    have hO : IsOpen O := hU.inter t.open_baseSet
    have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
    let E := t.localFrame b
    let V : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![A, B]
    have hV (j : Fin 2) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (V j)) O := by
      fin_cases j
      · exact hA.mono Set.inter_subset_left
      · exact hB.mono Set.inter_subset_left
    have hE (j : Fin n) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (E j)) O :=
      (t.contMDiffOn_localFrame_baseSet (n := ∞) b j).mono Set.inter_subset_right
    have hZO (j : Fin (k + 1)) := (hZ j).mono (t := O) Set.inter_subset_left
    have hUp {W : (y : M) → TangentSpace (𝓡 n) y}
        (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% W) O) (j : Fin (k + 1)) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Function.update Z i W j)) O := by
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hW
      · simpa only [Function.update_of_ne hji] using hZO j
    have hSum (s : Finset (Fin n))
        (W : Fin n → (y : M) → TangentSpace (𝓡 n) y)
        (hW : ∀ j ∈ s, ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (W j)) O) :
        covariantTensorDerivativeOnFields D T
          (Function.update Z i (fun y ↦ ∑ j ∈ s, W j y)) x =
            ∑ j ∈ s, covariantTensorDerivativeOnFields D T (Function.update Z i (W j)) x := by
      induction s using Finset.induction_on with
      | empty =>
        simpa only [Finset.sum_empty, Pi.smul_def', zero_smul, zero_mul] using!
          covariantTensorDerivativeOnFields_update_smul D hT hO hZO (hZO i)
            (f := fun _ ↦ (0 : ℝ)) contMDiffOn_const i hxO
      | insert j s hj ih =>
        have hWs (l : Fin n) (hl : l ∈ s) := hW l (Finset.mem_insert_of_mem hl)
        have hs := ContMDiffOn.sum_section hWs
        have ha := covariantTensorDerivativeOnFields_update_add D hT hO hZO
          (hW j (Finset.mem_insert_self j s)) hs i hxO
        rw [ih hWs] at ha
        simpa only [Finset.sum_insert hj, Pi.add_def] using! ha
    let C (a : Fin 2) (j : Fin n) := fun y ↦ t.localFrameCoeff (𝓡 n) b j y (V a y)
    have hC (a : Fin 2) (j : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C a j) O :=
      contMDiffOn_localFrameCoeff b hO Set.inter_subset_right (hV a) j
    have hS (a : Fin 2) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (fun y ↦ ∑ j, C a j y • E j y)) O :=
      ContMDiffOn.sum_section fun j _ ↦ (hC a j).smul_section (hE j)
    have hR (a : Fin 2) :
        covariantTensorDerivativeOnFields D T (Function.update Z i (V a)) x =
          ∑ j, C a j x *
            covariantTensorDerivativeOnFields D T (Function.update Z i (E j)) x := by
      calc
        _ = covariantTensorDerivativeOnFields D T
            (Function.update Z i (fun y ↦ ∑ j, C a j y • E j y)) x := by
          apply covariantTensorDerivativeOnFields_congr D hT hO
            (hUp (hV a)) (hUp (hS a)) ?_ hxO
          intro j y hy
          by_cases hji : j = i
          · subst j
            simp only [Function.update_self]
            exact t.eq_sum_localFrameCoeff_smul (b := b) hy.2
          · simp only [Function.update_of_ne hji]
        _ = ∑ j, covariantTensorDerivativeOnFields D T
            (Function.update Z i (fun y ↦ C a j y • E j y)) x :=
          hSum Finset.univ _ (fun j _ ↦ (hC a j).smul_section (hE j))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          exact covariantTensorDerivativeOnFields_update_smul D hT hO hZO
            (hE j) (hC a j) i hxO
    change covariantTensorDerivativeOnFields D T (Function.update Z i (V 0)) x =
      covariantTensorDerivativeOnFields D T (Function.update Z i (V 1)) x
    rw [hR 0, hR 1]
    apply Finset.sum_congr rfl
    intro j _
    change t.localFrameCoeff (𝓡 n) b j x (A x) * _ =
      t.localFrameCoeff (𝓡 n) b j x (B x) * _
    rw [he]
  let W (s : Finset (Fin (k + 1))) (j : Fin (k + 1)) := if j ∈ s then Y j else X j
  have hW (s : Finset (Fin (k + 1))) (j : Fin (k + 1)) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (W s j)) U := by
    by_cases hj : j ∈ s
    · simpa only [W, if_pos hj] using hY j
    · simpa only [W, if_neg hj] using hX j
  have hReplace (s : Finset (Fin (k + 1))) :
      covariantTensorDerivativeOnFields D T (W s) x =
        covariantTensorDerivativeOnFields D T X x := by
    induction s using Finset.induction_on with
    | empty => simp [W]
    | insert i s hi ih =>
      have hWi : W s i x = Y i x := by simpa only [W, if_neg hi] using hXY i
      have htup : W (insert i s) = Function.update (W s) i (Y i) := by
        funext j
        by_cases hji : j = i <;> simp [W, hji]
      rw [htup]
      have h := hOne (W s) (hW s) i (W s i) (Y i) (hW s i) (hY i) hWi
      simp only [Function.update_eq_self] at h
      exact h.symm.trans ih
  simpa [W] using (hReplace Finset.univ).symm

theorem covariantTensorDerivativeOnFields_eq (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) {x : M} (hx : x ∈ U) :
    covariantTensorDerivativeOnFields D T X x =
      D.covariantTensorDerivative T x (fun i ↦ X i x) := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let E := fun i : Fin (k + 1) ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (X i x)
  have hE (i : Fin (k + 1)) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (E i)) O :=
    (contMDiffOn_extend_baseSet (X i x)).mono Set.inter_subset_right
  have h := covariantTensorDerivativeOnFields_congr_at D hT hO
    (fun i ↦ (hX i).mono Set.inter_subset_left) hE hxO
    (fun _ ↦ (FiberBundle.extend_apply_self _ _).symm)
  simpa only [covariantTensorDerivativeOnFields, LeviCivitaData.covariantTensorDerivative,
    E, FiberBundle.extend_apply_self] using! h

theorem isSmoothCovariantTensor_covariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.covariantTensorDerivative T) := by
  classical
  constructor
  · intro x
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    let E := fun v : TangentSpace (𝓡 n) x ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    have hE (v : TangentSpace (𝓡 n) x) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (E v)) t.baseSet := contMDiffOn_extend_baseSet v
    have hUp (v : Fin (k + 1) → TangentSpace (𝓡 n) x) (i : Fin (k + 1))
        {A : (y : M) → TangentSpace (𝓡 n) y}
        (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% A) t.baseSet) (j : Fin (k + 1)) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Function.update (fun l ↦ E (v l)) i A j)) t.baseSet := by
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hA
      · simpa only [Function.update_of_ne hji] using hE (v j)
    have hEval (v : Fin (k + 1) → TangentSpace (𝓡 n) x) (i : Fin (k + 1))
        {A : (y : M) → TangentSpace (𝓡 n) y}
        (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% A) t.baseSet) :
        covariantTensorDerivativeOnFields D T (Function.update (fun l ↦ E (v l)) i A) x =
          D.covariantTensorDerivative T x (Function.update v i (A x)) := by
      rw [covariantTensorDerivativeOnFields_eq D hT t.open_baseSet (hUp v i hA) hx]
      congr 1
      funext j
      by_cases hji : j = i <;> simp [hji, E]
    refine ⟨MultilinearMap.mk' (R := ℝ) (D.covariantTensorDerivative T x)
      ?_ ?_, fun _ ↦ rfl⟩
    · intro v i a b
      have h := covariantTensorDerivativeOnFields_update_add D hT t.open_baseSet
        (fun j ↦ hE (v j)) (hE a) (hE b) i hx
      rw [hEval v i ((hE a).add_section (hE b)), hEval v i (hE a), hEval v i (hE b)] at h
      simpa only [Pi.add_apply, E, FiberBundle.extend_apply_self] using! h
    · intro v i c a
      have h := covariantTensorDerivativeOnFields_update_smul D hT t.open_baseSet
        (fun j ↦ hE (v j)) (hE a) (f := fun _ ↦ c) contMDiffOn_const i hx
      rw [hEval v i (contMDiffOn_const.smul_section (hE a)), hEval v i (hE a)] at h
      simpa only [Pi.smul_apply', E, FiberBundle.extend_apply_self, smul_eq_mul] using! h
  · intro U hU X hX
    apply (contMDiffOn_covariantTensorDerivativeOnFields D hT hU hX).congr
    intro x hx
    exact (covariantTensorDerivativeOnFields_eq D hT hU hX hx).symm

end PoincareConjecture.RicciFlowAnalysis
