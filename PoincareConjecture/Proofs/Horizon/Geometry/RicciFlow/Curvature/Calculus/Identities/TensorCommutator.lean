import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.CurvaturePointwise
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.ScalarBracket











set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_field_derivative (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U) {A : (x : M) → TangentSpace (𝓡 n) x}
    {V : Fin k → (x : M) → TangentSpace (𝓡 n) x}
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ V i y)) x (A x) =
      D.covariantTensorDerivative T x (Fin.cons (A x) (fun i ↦ V i x)) +
        ∑ i, T x (Function.update (fun j ↦ V j x) i (D.connection (V i) x (A x))) := by
  let AV : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons A V
  have hAV (i : Fin (k + 1)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (AV i)) U := by
    cases i using Fin.cases with
    | zero => exact hA
    | succ i => exact hV i
  have he := covariantTensorDerivativeOnFields_eq D hT hU hAV hx
  have hpoint : (fun i ↦ AV i x) = Fin.cons (A x) (fun i ↦ V i x) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [hpoint] at he
  simp only [covariantTensorDerivativeOnFields, AV, Fin.cons_succ, Fin.cons_zero] at he
  exact sub_eq_iff_eq_add.mp he

set_option maxHeartbeats 3000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_commutator_on_fields (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U) {A B : (x : M) → TangentSpace (𝓡 n) x}
    {V : Fin k → (x : M) → TangentSpace (𝓡 n) x}
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% B) U)
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) {x : M} (hx : x ∈ U) :
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons (A x) (Fin.cons (B x) (fun i ↦ V i x))) -
      D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons (B x) (Fin.cons (A x) (fun i ↦ V i x))) =
      -(∑ i, T x (Function.update (fun j ↦ V j x) i
        (D.curvatureOnFields A B (V i) x))) := by
  classical
  let Smooth (Z : (y : M) → TangentSpace (𝓡 n) y) :=
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U
  let W : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![A, B]
  have hW (i : Fin 2) : Smooth (W i) := by
    fin_cases i
    · exact hA
    · exact hB
  let C (i : Fin 2) (Z : (y : M) → TangentSpace (𝓡 n) y) :=
    fun y ↦ D.connection Z y (W i y)
  have hC (i : Fin 2) (a : Fin k) : Smooth (C i (V a)) := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g
    intro v
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hye : y ∈ U ∩ e.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing D (hU.inter e.open_baseSet)
      ((hW i).mono Set.inter_subset_left) ((hV a).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)).contMDiffAt
        ((hU.inter e.open_baseSet).mem_nhds hye)
  have hCons {l : ℕ} {P : (y : M) → TangentSpace (𝓡 n) y}
      {S : Fin l → (y : M) → TangentSpace (𝓡 n) y}
      (hP : Smooth P) (hS : ∀ i, Smooth (S i)) :
      ∀ i, Smooth ((Fin.cons P S : Fin (l + 1) →
        (y : M) → TangentSpace (𝓡 n) y) i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact hP
    | succ i => exact hS i
  have hPointCons {l : ℕ} (P : (y : M) → TangentSpace (𝓡 n) y)
      (S : Fin l → (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ (Fin.cons P S : Fin (l + 1) →
        (z : M) → TangentSpace (𝓡 n) z) i y) = Fin.cons (P y) (fun i ↦ S i y) := by
    funext i
    cases i using Fin.cases <;> rfl
  have hPointUpdate (S : Fin k → (y : M) → TangentSpace (𝓡 n) y)
      (a : Fin k) (P : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ Function.update S a P i y) =
        Function.update (fun i ↦ S i y) a (P y) := by
    funext i
    by_cases hi : i = a <;> simp [Function.update, hi]
  let Z (i : Fin 2) (a : Fin k) := Function.update V a (C i (V a))
  have hZ (i : Fin 2) (a b : Fin k) : Smooth (Z i a b) := by
    by_cases hb : b = a
    · subst b
      simpa only [Z, Function.update_self] using hC i a
    · simpa only [Z, Function.update_of_ne hb] using hV b
  let K := D.covariantTensorDerivative T
  let K2 := D.covariantTensorDerivative K
  have hK : IsSmoothCovariantTensor K := isSmoothCovariantTensor_covariantTensorDerivative D hT
  let f := fun y ↦ T y (fun a ↦ V a y)
  let F (i : Fin 2) := fun y ↦ mvfderiv (𝓡 n) f y (W i y)
  have hF (i : Fin 2) : F i =ᶠ[𝓝 x]
      (fun y ↦ K y (Fin.cons (W i y) (fun a ↦ V a y)) +
        ∑ a, T y (fun b ↦ Z i a b y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [F, f, K, Z, hPointUpdate, C] using
      tensor_field_derivative D hT hU (hW i) hV hy
  have hKs (i : Fin 2) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ K y (Fin.cons (W i y) (fun a ↦ V a y))) U := by
    simpa only [hPointCons] using hK.2 U hU _ (hCons (hW i) hV)
  have hTs (i : Fin 2) (a : Fin k) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ T y (fun b ↦ Z i a b y)) U := hT.2 U hU _ (hZ i a)
  have hKd (i : Fin 2) := ((hKs i).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hTd (i : Fin 2) (a : Fin k) :=
    ((hTs i a).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hSd (i : Fin 2) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ ∑ a, T y (fun b ↦ Z i a b y)) x := by
    simpa only [Finset.sum_fn] using MDifferentiableAt.sum (t := Finset.univ)
      (fun a _ ↦ hTd i a)
  have hSum (i j : Fin 2) :
      mvfderiv (𝓡 n) (fun y ↦ ∑ a, T y (fun b ↦ Z j a b y)) x (W i x) =
        ∑ a, mvfderiv (𝓡 n) (fun y ↦ T y (fun b ↦ Z j a b y)) x (W i x) := by
    have hs (s : Finset (Fin k)) :
        mvfderiv (𝓡 n) (fun y ↦ ∑ a ∈ s, T y (fun b ↦ Z j a b y)) x (W i x) =
          ∑ a ∈ s, mvfderiv (𝓡 n) (fun y ↦ T y (fun b ↦ Z j a b y)) x (W i x) := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, mvfderiv_const, zero_apply]
      | @insert a s ha ih =>
        have hss : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
            (fun y ↦ ∑ b ∈ s, T y (fun c ↦ Z j b c y)) x := by
          have hh : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
              (fun y ↦ ∑ b ∈ s, T y (fun c ↦ Z j b c y)) x :=
            ContMDiffAt.sum (fun b _ ↦ (hTs j b).contMDiffAt (hU.mem_nhds hx))
          exact hh.mdifferentiableAt (by simp)
        simp only [Finset.sum_insert ha]
        erw [mvfderiv_add (hTd j a) hss, add_apply, ih]
    exact hs Finset.univ
  have hKDiff (i j : Fin 2) :
      mvfderiv (𝓡 n) (fun y ↦ K y (Fin.cons (W j y) (fun a ↦ V a y))) x (W i x) =
        K2 x (Fin.cons (W i x) (Fin.cons (W j x) (fun a ↦ V a x))) +
          K x (Fin.cons (C i (W j) x) (fun a ↦ V a x)) +
          ∑ a, K x (Fin.cons (W j x)
            (Function.update (fun b ↦ V b x) a (C i (V a) x))) := by
    have he := tensor_field_derivative D hK hU (hW i) (hCons (hW j) hV) hx
    simp only [hPointCons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.update_cons_zero, ← Fin.cons_update] at he
    change _ = K2 x _ + (K x _ + ∑ a, K x _) at he
    simpa only [add_assoc, C] using he
  let H (i j : Fin 2) (a b : Fin k) :=
    T x (Function.update (Function.update (fun l ↦ V l x) a (C j (V a) x)) b
      (C i (Z j a b) x))
  have hTDiff (i j : Fin 2) (a : Fin k) :
      mvfderiv (𝓡 n) (fun y ↦ T y (fun b ↦ Z j a b y)) x (W i x) =
        K x (Fin.cons (W i x) (Function.update (fun b ↦ V b x) a (C j (V a) x))) +
          ∑ b, H i j a b := by
    simpa only [Z, hPointUpdate, H, K, C] using
      tensor_field_derivative D hT hU (hW i) (hZ j a) hx
  have hSecond (i j : Fin 2) : mvfderiv (𝓡 n) (F j) x (W i x) =
      K2 x (Fin.cons (W i x) (Fin.cons (W j x) (fun a ↦ V a x))) +
        K x (Fin.cons (C i (W j) x) (fun a ↦ V a x)) +
        (∑ a, K x (Fin.cons (W j x) (Function.update (fun b ↦ V b x) a (C i (V a) x)))) +
        (∑ a, K x (Fin.cons (W i x) (Function.update (fun b ↦ V b x) a (C j (V a) x)))) +
        ∑ a, ∑ b, H i j a b := by
    have he : mvfderiv (𝓡 n) (F j) x = mvfderiv (𝓡 n)
        (fun y ↦ K y (Fin.cons (W j y) (fun a ↦ V a y)) +
          ∑ a, T y (fun b ↦ Z j a b y)) x := (hF j).mfderiv_eq
    rw [he]
    erw [mvfderiv_add (hKd j) (hSd j), add_apply]
    rw [hKDiff, hSum]
    simp only [hTDiff, Finset.sum_add_distrib]
    ring
  have hDouble : (∑ a, ∑ b, H 0 1 a b) - (∑ a, ∑ b, H 1 0 a b) =
      (∑ a, T x (Function.update (fun b ↦ V b x) a (C 0 (C 1 (V a)) x))) -
        ∑ a, T x (Function.update (fun b ↦ V b x) a (C 1 (C 0 (V a)) x)) := by
    have hterm (a b : Fin k) : H 0 1 a b - H 1 0 b a =
        if b = a then
          T x (Function.update (fun l ↦ V l x) a (C 0 (C 1 (V a)) x)) -
            T x (Function.update (fun l ↦ V l x) a (C 1 (C 0 (V a)) x))
        else 0 := by
      by_cases hb : b = a
      · subst b
        simp only [H, Z, Function.update_self, Function.update_idem, if_true]
      · simp only [H, Z, Function.update_of_ne hb, Function.update_of_ne (Ne.symm hb),
          if_neg hb]
        rw [Function.update_comm (Ne.symm hb), sub_self]
    calc
      _ = ∑ a, ∑ b, (H 0 1 a b - H 1 0 b a) := by
        simp only [Finset.sum_sub_distrib]
        rw [Finset.sum_comm (f := fun a b ↦ H 1 0 b a)]
      _ = _ := by simp [hterm, Finset.sum_sub_distrib]
  let br := VectorField.mlieBracket (𝓡 n) A B
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  have hbr : Smooth br := by
    intro y hy
    exact (((hA y hy).contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (m := ⊤) (n := ⊤) ((hB y hy).contMDiffAt (hU.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  have hBracket : C 0 (W 1) x - C 1 (W 0) x = br x :=
    connection_commutator D
      (((hA x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      (((hB x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
  have hKB : K x (Fin.cons (br x) (fun a ↦ V a x)) =
      K x (Fin.cons (C 0 (W 1) x) (fun a ↦ V a x)) -
        K x (Fin.cons (C 1 (W 0) x) (fun a ↦ V a x)) := by
    obtain ⟨L, hL⟩ := hK.1 x
    rw [← hBracket]
    simp only [hL]
    simpa only [Fin.update_cons_zero] using L.map_update_sub
      (Fin.cons (C 0 (W 1) x) (fun a ↦ V a x)) 0 (C 0 (W 1) x) (C 1 (W 0) x)
  have hcomm := mvfderiv_mlieBracket hU (hT.2 U hU V hV) hA hB hx
  have hbrdiff := tensor_field_derivative D hT hU hbr hV hx
  change mvfderiv (𝓡 n) f x (br x) =
    mvfderiv (𝓡 n) (F 1) x (W 0 x) - mvfderiv (𝓡 n) (F 0) x (W 1 x) at hcomm
  rw [hSecond, hSecond] at hcomm
  change mvfderiv (𝓡 n) f x (br x) = K x _ + _ at hbrdiff
  rw [hKB] at hbrdiff
  have hout :
      K2 x (Fin.cons (W 0 x) (Fin.cons (W 1 x) (fun a ↦ V a x))) -
        K2 x (Fin.cons (W 1 x) (Fin.cons (W 0 x) (fun a ↦ V a x))) =
      (∑ a, T x (Function.update (fun b ↦ V b x) a (D.connection (V a) x (br x)))) -
        ((∑ a, ∑ b, H 0 1 a b) - (∑ a, ∑ b, H 1 0 a b)) := by
    linarith only [hcomm, hbrdiff]
  have hR (a : Fin k) : T x (Function.update (fun b ↦ V b x) a
        (D.curvatureOnFields A B (V a) x)) =
      T x (Function.update (fun b ↦ V b x) a (C 0 (C 1 (V a)) x)) -
        T x (Function.update (fun b ↦ V b x) a (C 1 (C 0 (V a)) x)) -
        T x (Function.update (fun b ↦ V b x) a (D.connection (V a) x (br x))) := by
    obtain ⟨L, hL⟩ := hT.1 x
    simp only [LeviCivitaData.curvatureOnFields, hL, L.map_update_sub]
    rfl
  rw [hDouble] at hout
  change K2 x (Fin.cons (W 0 x) (Fin.cons (W 1 x) (fun a ↦ V a x))) -
      K2 x (Fin.cons (W 1 x) (Fin.cons (W 0 x) (fun a ↦ V a x))) = _
  rw [hout]
  simp only [hR, Finset.sum_sub_distrib]
  ring

theorem covariantTensorDerivative_commutator (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (a b : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative T 2 x (Fin.cons a (Fin.cons b v)) -
      D.iteratedCovariantTensorDerivative T 2 x (Fin.cons b (Fin.cons a v)) =
      -(∑ i, T x (Function.update v i (D.curvature x a b (v i)))) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let A := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let B := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let V := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) e.baseSet := contMDiffOn_extend_baseSet a
  have hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% B) e.baseSet := contMDiffOn_extend_baseSet b
  have hV (i : Fin k) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V i)) e.baseSet :=
    contMDiffOn_extend_baseSet (v i)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have he := tensor_commutator_on_fields D hT e.open_baseSet hA hB hV hx
  have hR (i : Fin k) : D.curvatureOnFields A B (V i) x = D.curvature x a b (v i) := by
    simpa only [A, B, V, FiberBundle.extend_apply_self] using
      curvatureOnFields_eq_curvature D e.open_baseSet hA hB (hV i) hx
  simpa only [hR, A, B, V, FiberBundle.extend_apply_self,
    LeviCivitaData.iteratedCovariantTensorDerivative] using he

end PoincareConjecture.RicciFlowAnalysis
