import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.TensorCommutator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.TensorNullMinimum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity











set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem exists_local_fields_connection_zero
    (D : LeviCivitaData g) {ι : Type} [Finite ι]
    (x : M) (v : ι → TangentSpace (𝓡 n) x) :
    ∃ (U : Set M) (X : ι → (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ x ∈ U ∧
      (∀ i, ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X i)) U) ∧
      (∀ i, X i x = v i) ∧ ∀ i, D.connection (X i) x = 0 := by
  classical
  choose U X hU hx hX hval hzero using fun i ↦
    exists_local_field_connection_zero D x (v i)
  refine ⟨⋂ i, U i, X, isOpen_iInter_of_finite hU, mem_iInter.mpr hx, ?_, hval, hzero⟩
  intro i
  exact (hX i).mono (iInter_subset U i)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_field_derivative (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {V : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hV : ∀ i, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V i)) U)
    {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ V i.succ y)) x (V 0 x) =
      D.covariantTensorDerivative T x (fun i ↦ V i x) +
        ∑ i, T x (Function.update (fun j ↦ V j.succ x) i
          (D.connection (V i.succ) x (V 0 x))) := by
  have h := covariantTensorDerivativeOnFields_eq D hT hU hV hx
  exact sub_eq_iff_eq_add.mp h

set_option backward.isDefEq.respectTransparency false in
private theorem curvature_output_derivative_pairing (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    {V : Fin 5 → (y : M) → TangentSpace (𝓡 n) y}
    (hV : ∀ i, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V i)) U)
    {x : M} (hx : x ∈ U)
    (hzero : ∀ i : Fin 4, D.connection (V i.succ) x (V 0 x) = 0) :
    g.inner x
        (D.connection (D.curvatureOnFields (V 1) (V 2) (V 4)) x (V 0 x))
        (V 3 x) =
      D.covariantTensorDerivative D.riemannEvaluation x (fun i ↦ V i x) := by
  classical
  have hRm := isSmoothCovariantTensor_riemannEvaluation D
  have h := tensor_field_derivative D hRm hU hV hx
  obtain ⟨L, hL⟩ := hRm.1 x
  have hcorr (i : Fin 4) : D.riemannEvaluation x
      (Function.update (fun j ↦ V j.succ x) i
        (D.connection (V i.succ) x (V 0 x))) = 0 := by
    rw [hzero, hL, L.map_update_zero]
  simp only [hcorr, Finset.sum_const_zero, add_zero] at h
  have he : (fun y ↦ D.riemannEvaluation y (fun i ↦ V i.succ y)) =ᶠ[𝓝 x]
      (fun y ↦ g.inner y (D.curvatureOnFields (V 1) (V 2) (V 4) y) (V 3 y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [curvatureOnFields_eq_curvature D hU (hV 1) (hV 2) (hV 4) hy]
    rfl
  have hC := contMDiffOn_curvatureOnFields D hU (hV 1) (hV 2) (hV 4)
  have hmetric := metric_derivative_pairing D (V 0)
    (hC.contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
    ((hV 3).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
  have hz : D.connection (V 3) x (V 0 x) = 0 := hzero 2
  simp only [hz, map_zero, add_zero] at hmetric
  have hder : mvfderiv (𝓡 n)
      (fun y ↦ D.riemannEvaluation y (fun i ↦ V i.succ y)) x =
      mvfderiv (𝓡 n)
        (fun y ↦ g.inner y (D.curvatureOnFields (V 1) (V 2) (V 4) y) (V 3 y)) x :=
    he.mfderiv_eq
  rw [hder, hmetric] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem mvfderiv_fin_sum {k : ℕ}
    (s : Finset (Fin k)) {f : Fin k → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f i) x)
    (c : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ i ∈ s, f i y) x c =
      ∑ i ∈ s, mvfderiv (𝓡 n) (f i) x c := by
  have h := (HasMFDerivAt.sum (fun i hi ↦ (hf i hi).hasMFDerivAt)).mfderiv
  have he : (∑ i ∈ s, f i) = (fun y ↦ ∑ i ∈ s, f i y) := by
    funext y
    simp only [Finset.sum_fn]
  rw [he] at h
  simpa [mvfderiv, NormedSpace.fromTangentSpace, Finset.sum_fn] using!
    congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ ↦ L c) h

set_option maxHeartbeats 6000000 in

set_option backward.isDefEq.respectTransparency false in
theorem thirdCovariantTensorDerivative_commutator (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (c a d : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    D.iteratedCovariantTensorDerivative T 3 x
        (Fin.cons c (Fin.cons a (Fin.cons d v))) -
      D.iteratedCovariantTensorDerivative T 3 x
        (Fin.cons c (Fin.cons d (Fin.cons a v))) =
      -(∑ r, ∑ q,
        (D.covariantTensorDerivative D.riemannEvaluation x
            ![c, a, d, b q, v r] * T x (Function.update v r (b q)) +
          D.curvatureTensor x a d (b q) (v r) *
            D.covariantTensorDerivative T x
              (Fin.cons c (Function.update v r (b q))))) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  obtain ⟨U, W, hU, hx, hW, hWx, hDW⟩ := exists_local_fields_connection_zero D x
    (Sum.elim (Fin.cons c (Fin.cons a (Fin.cons d v))) b)
  let X := W (Sum.inl 0)
  let A := W (Sum.inl 1)
  let B := W (Sum.inl 2)
  let V := fun r : Fin k ↦ W (Sum.inl r.succ.succ.succ)
  let E := fun q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ↦ W (Sum.inr q)
  let Smooth (Z : (y : M) → TangentSpace (𝓡 n) y) :=
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U
  have hX : Smooth X := hW (Sum.inl 0)
  have hA : Smooth A := hW (Sum.inl 1)
  have hB : Smooth B := hW (Sum.inl 2)
  have hV (r : Fin k) : Smooth (V r) := hW (Sum.inl r.succ.succ.succ)
  have hE (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : Smooth (E q) :=
    hW (Sum.inr q)
  have hXx : X x = c := hWx (Sum.inl 0)
  have hAx : A x = a := hWx (Sum.inl 1)
  have hBx : B x = d := hWx (Sum.inl 2)
  have hVx (r : Fin k) : V r x = v r := hWx (Sum.inl r.succ.succ.succ)
  have hEx (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : E q x = b q :=
    hWx (Sum.inr q)
  have hDA : D.connection A x = 0 := hDW (Sum.inl 1)
  have hDB : D.connection B x = 0 := hDW (Sum.inl 2)
  have hDV (r : Fin k) : D.connection (V r) x = 0 := hDW (Sum.inl r.succ.succ.succ)
  have hDE (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.connection (E q) x = 0 := hDW (Sum.inr q)
  have hCons {l : ℕ} {P : (y : M) → TangentSpace (𝓡 n) y}
      {Z : Fin l → (y : M) → TangentSpace (𝓡 n) y}
      (hP : Smooth P) (hZ : ∀ i, Smooth (Z i)) :
      ∀ i, Smooth ((Fin.cons P Z : Fin (l + 1) →
        (y : M) → TangentSpace (𝓡 n) y) i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact hP
    | succ i => exact hZ i
  have hPoint {l : ℕ} (P : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin l → (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ (Fin.cons P Z : Fin (l + 1) →
        (z : M) → TangentSpace (𝓡 n) z) i y) =
        Fin.cons (P y) (fun i ↦ Z i y) := by
    funext i
    cases i using Fin.cases <;> rfl
  have hPointUpdate (Z : Fin k → (y : M) → TangentSpace (𝓡 n) y)
      (r : Fin k) (P : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ Function.update Z r P i y) =
        Function.update (fun i ↦ Z i y) r (P y) := by
    funext i
    by_cases hi : i = r <;> simp [Function.update, hi]
  have hDiff {l : ℕ} {S : CovariantTensorEvaluation n M l}
      (hS : IsSmoothCovariantTensor S)
      {Z : Fin l → (y : M) → TangentSpace (𝓡 n) y}
      (hZ : ∀ i, Smooth (Z i)) :
      mvfderiv (𝓡 n) (fun y ↦ S y (fun i ↦ Z i y)) x c =
        D.covariantTensorDerivative S x (Fin.cons c (fun i ↦ Z i x)) +
          ∑ i, S x (Function.update (fun j ↦ Z j x) i
            (D.connection (Z i) x c)) := by
    simpa only [Fin.cons_zero, Fin.cons_succ, hPoint, hXx] using
      tensor_field_derivative D hS hU (hCons hX hZ) hx
  have hDiffZero {l : ℕ} {S : CovariantTensorEvaluation n M l}
      (hS : IsSmoothCovariantTensor S)
      {Z : Fin l → (y : M) → TangentSpace (𝓡 n) y}
      (hZ : ∀ i, Smooth (Z i)) (hDZ : ∀ i, D.connection (Z i) x = 0) :
      mvfderiv (𝓡 n) (fun y ↦ S y (fun i ↦ Z i y)) x c =
        D.covariantTensorDerivative S x (Fin.cons c (fun i ↦ Z i x)) := by
    have he := hDiff hS hZ
    obtain ⟨L, hL⟩ := hS.1 x
    have hz (i : Fin l) : S x (Function.update (fun j ↦ Z j x) i
        (D.connection (Z i) x c)) = 0 := by
      rw [hDZ, zero_apply, hL, L.map_update_zero]
    simpa only [hz, Finset.sum_const_zero, add_zero] using he
  let K := D.covariantTensorDerivative T
  let K2 := D.covariantTensorDerivative K
  have hK : IsSmoothCovariantTensor K := isSmoothCovariantTensor_covariantTensorDerivative D hT
  have hK2 : IsSmoothCovariantTensor K2 := isSmoothCovariantTensor_covariantTensorDerivative D hK
  let C := fun r : Fin k ↦ D.curvatureOnFields A B (V r)
  have hC (r : Fin k) : Smooth (C r) :=
    contMDiffOn_curvatureOnFields D hU hA hB (hV r)
  have hCx (r : Fin k) : C r x = D.curvature x a d (v r) := by
    simpa only [C, hAx, hBx, hVx] using
      curvatureOnFields_eq_curvature D hU hA hB (hV r) hx
  have hCpair (r : Fin k) (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.inner x (C r x) (b q) = D.curvatureTensor x a d (b q) (v r) := by
    rw [hCx]
    rfl
  have hDCpair (r : Fin k) (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.inner x (D.connection (C r) x c) (b q) =
        D.covariantTensorDerivative D.riemannEvaluation x ![c, a, d, b q, v r] := by
    let Z : Fin 5 → (y : M) → TangentSpace (𝓡 n) y := ![X, A, B, E q, V r]
    have hZ (i : Fin 5) : Smooth (Z i) := by
      fin_cases i
      · exact hX
      · exact hA
      · exact hB
      · exact hE q
      · exact hV r
    have hz (i : Fin 4) : D.connection (Z i.succ) x (Z 0 x) = 0 := by
      fin_cases i
      · change D.connection A x (X x) = 0
        rw [hDA, zero_apply]
      · change D.connection B x (X x) = 0
        rw [hDB, zero_apply]
      · change D.connection (E q) x (X x) = 0
        rw [hDE, zero_apply]
      · change D.connection (V r) x (X x) = 0
        rw [hDV, zero_apply]
    have he := curvature_output_derivative_pairing D hU hZ hx hz
    have hp : (fun i ↦ Z i x) = ![c, a, d, b q, v r] := by
      funext i
      fin_cases i
      · exact hXx
      · exact hAx
      · exact hBx
      · exact hEx q
      · exact hVx r
    rw [hp] at he
    change g.inner x (D.connection (C r) x (X x)) (E q x) = _ at he
    simpa only [hXx, hEx] using he
  have hExpand {l : ℕ}
      (L : MultilinearMap ℝ (fun _ : Fin l ↦ TangentSpace (𝓡 n) x) ℝ)
      (w : Fin l → TangentSpace (𝓡 n) x) (r : Fin l)
      (z : TangentSpace (𝓡 n) x) :
      L (Function.update w r z) =
        ∑ q, g.inner x z (b q) * L (Function.update w r (b q)) := by
    have hb : (∑ q, g.inner x z (b q) • b q) = z := by
      change (∑ q, inner ℝ z (b q) • b q) = z
      simpa only [real_inner_comm] using b.sum_repr' z
    conv_lhs => rw [← hb]
    simp only [L.map_update_sum, L.map_update_smul, smul_eq_mul]
  let Z := fun r : Fin k ↦ Function.update V r (C r)
  have hZ (r i : Fin k) : Smooth (Z r i) := by
    by_cases hi : i = r
    · subst i
      simpa only [Z, Function.update_self] using hC r
    · simpa only [Z, Function.update_of_ne hi] using hV i
  have hTd (r : Fin k) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ T y (fun i ↦ Z r i y)) x :=
    ((hT.2 U hU _ (hZ r)).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hInserted (r : Fin k) :
      mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ Z r i y)) x c =
        ∑ q,
          (D.covariantTensorDerivative D.riemannEvaluation x ![c, a, d, b q, v r] *
              T x (Function.update v r (b q)) +
            D.curvatureTensor x a d (b q) (v r) *
              K x (Fin.cons c (Function.update v r (b q)))) := by
    have he := hDiff hT (hZ r)
    have hp : (fun i ↦ Z r i x) = Function.update v r (C r x) := by
      simp only [Z, hPointUpdate, hVx]
    rw [hp] at he
    obtain ⟨L, hL⟩ := hT.1 x
    have hcorr (i : Fin k) :
        T x (Function.update (Function.update v r (C r x)) i
          (D.connection (Z r i) x c)) =
        if i = r then T x (Function.update v r (D.connection (C r) x c)) else 0 := by
      by_cases hi : i = r
      · subst i
        simp only [Z, Function.update_self, Function.update_idem, if_true]
      · simp only [Z, Function.update_of_ne hi, hDV, zero_apply, hL,
          L.map_update_zero, if_neg hi]
    simp only [hcorr, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
    obtain ⟨LK, hLK⟩ := hK.1 x
    have hfirst : K x (Fin.cons c (Function.update v r (C r x))) =
        ∑ q, D.curvatureTensor x a d (b q) (v r) *
          K x (Fin.cons c (Function.update v r (b q))) := by
      simpa only [hLK, Fin.cons_update, hCpair] using
        hExpand LK (Fin.cons c v) r.succ (C r x)
    have hsecond : T x (Function.update v r (D.connection (C r) x c)) =
        ∑ q, D.covariantTensorDerivative D.riemannEvaluation x ![c, a, d, b q, v r] *
          T x (Function.update v r (b q)) := by
      simpa only [hL, hDCpair] using hExpand L v r (D.connection (C r) x c)
    change _ = K x _ + _ at he
    rw [hfirst, hsecond, ← Finset.sum_add_distrib] at he
    rw [he]
    apply Finset.sum_congr rfl
    intro q _
    ring
  let S1 : Fin (k + 2) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons A (Fin.cons B V)
  let S2 : Fin (k + 2) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons B (Fin.cons A V)
  have hS1 : ∀ i, Smooth (S1 i) := hCons hA (hCons hB hV)
  have hS2 : ∀ i, Smooth (S2 i) := hCons hB (hCons hA hV)
  have hDS1 (i : Fin (k + 2)) : D.connection (S1 i) x = 0 := by
    cases i using Fin.cases with
    | zero => exact hDA
    | succ i =>
      cases i using Fin.cases with
      | zero => exact hDB
      | succ i => exact hDV i
  have hDS2 (i : Fin (k + 2)) : D.connection (S2 i) x = 0 := by
    cases i using Fin.cases with
    | zero => exact hDB
    | succ i =>
      cases i using Fin.cases with
      | zero => exact hDA
      | succ i => exact hDV i
  let f1 := fun y ↦ K2 y (fun i ↦ S1 i y)
  let f2 := fun y ↦ K2 y (fun i ↦ S2 i y)
  have hf1 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f1 x :=
    ((hK2.2 U hU _ hS1).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hf2 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f2 x :=
    ((hK2.2 U hU _ hS2).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdf1 : mvfderiv (𝓡 n) f1 x c =
      D.iteratedCovariantTensorDerivative T 3 x
        (Fin.cons c (Fin.cons a (Fin.cons d v))) := by
    simpa only [f1, S1, hPoint, hAx, hBx, hVx,
      LeviCivitaData.iteratedCovariantTensorDerivative, K2, K] using hDiffZero hK2 hS1 hDS1
  have hdf2 : mvfderiv (𝓡 n) f2 x c =
      D.iteratedCovariantTensorDerivative T 3 x
        (Fin.cons c (Fin.cons d (Fin.cons a v))) := by
    simpa only [f2, S2, hPoint, hAx, hBx, hVx,
      LeviCivitaData.iteratedCovariantTensorDerivative, K2, K] using hDiffZero hK2 hS2 hDS2
  have hgerm : (f1 - f2) =ᶠ[𝓝 x]
      (fun y ↦ -(∑ r, T y (fun i ↦ Z r i y))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hc (r : Fin k) : C r y = D.curvature y (A y) (B y) (V r y) :=
      curvatureOnFields_eq_curvature D hU hA hB (hV r) hy
    simpa only [Pi.sub_apply, f1, f2, S1, S2, hPoint, Z, hPointUpdate, hc,
      LeviCivitaData.iteratedCovariantTensorDerivative, K2, K] using
      covariantTensorDerivative_commutator D hT y (A y) (B y) (fun r ↦ V r y)
  have hder : mvfderiv (𝓡 n) (f1 - f2) x =
      mvfderiv (𝓡 n) (fun y ↦ -(∑ r, T y (fun i ↦ Z r i y))) x := hgerm.mfderiv_eq
  have hsum := mvfderiv_fin_sum Finset.univ (fun r _ ↦ hTd r) c
  have he := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ ↦ L c) hder
  rw [mvfderiv_sub hf1 hf2, sub_apply, hdf1, hdf2] at he
  simp only [mvfderiv_fun_neg, neg_apply, hsum, hInserted] at he
  exact he


end PoincareConjecture.RicciFlowAnalysis
