import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.TensorNullMinimum











set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 4000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem local_null_fields_diffusion (D : LeviCivitaData g)
    {k : ℕ} {S : CovariantTensorEvaluation n M k} (hS : IsSmoothCovariantTensor S)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (W : Fin k → (y : M) → TangentSpace (𝓡 n) y)
    (hW : ∀ i, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (W i)) U)
    (hDW : ∀ i, D.connection (W i) x = 0)
    (hker : ∀ i z, S x (Function.update (fun j ↦ W j x) i z) = 0)
    (hmin : IsLocalMin (fun y ↦ S y (fun i ↦ W i y)) x) :
    0 ≤ D.tensorLaplacian S x (fun i ↦ W i x) := by
  classical
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ e.baseSet
  have hO : IsOpen O := hU.inter e.open_baseSet
  have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let Smooth (Z : (y : M) → TangentSpace (𝓡 n) y) :=
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) O
  have hWO (i : Fin k) : Smooth (W i) := (hW i).mono inter_subset_left
  have hE (a : TangentSpace (𝓡 n) x) :
      Smooth (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) :=
    (contMDiffOn_extend_baseSet a).mono inter_subset_right
  have hCons {r : ℕ} {Z : (y : M) → TangentSpace (𝓡 n) y}
      {V : Fin r → (y : M) → TangentSpace (𝓡 n) y}
      (hZ : Smooth Z) (hV : ∀ i, Smooth (V i)) :
      ∀ i, Smooth ((Fin.cons Z V : Fin (r + 1) →
        (y : M) → TangentSpace (𝓡 n) y) i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact hZ
    | succ i => exact hV i
  have hUpdate {r : ℕ} {V : Fin r → (y : M) → TangentSpace (𝓡 n) y}
      {Z : (y : M) → TangentSpace (𝓡 n) y}
      (hV : ∀ i, Smooth (V i)) (hZ : Smooth Z) (i : Fin r) :
      ∀ j, Smooth (Function.update V i Z j) := by
    intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using hZ
    · simpa only [Function.update_of_ne h] using hV j
  have hPoint {r : ℕ} (Z : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin r → (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ (Fin.cons Z V : Fin (r + 1) →
        (z : M) → TangentSpace (𝓡 n) z) i y) =
        Fin.cons (Z y) (fun i ↦ V i y) := by
    funext i
    cases i using Fin.cases <;> rfl
  have hPointUpdate {r : ℕ} (V : Fin r → (y : M) → TangentSpace (𝓡 n) y)
      (i : Fin r) (Z : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun j ↦ Function.update V i Z j y) =
        Function.update (fun j ↦ V j y) i (Z y) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  have hDiff {r : ℕ} {T : CovariantTensorEvaluation n M r}
      (hT : IsSmoothCovariantTensor T)
      {Z : (y : M) → TangentSpace (𝓡 n) y}
      {V : Fin r → (y : M) → TangentSpace (𝓡 n) y}
      (hZ : Smooth Z) (hV : ∀ i, Smooth (V i)) {y : M} (hy : y ∈ O) :
      mvfderiv (𝓡 n) (fun z ↦ T z (fun i ↦ V i z)) y (Z y) =
        D.covariantTensorDerivative T y (Fin.cons (Z y) (fun i ↦ V i y)) +
          ∑ i, T y (Function.update (fun j ↦ V j y) i
            (D.connection (V i) y (Z y))) := by
    have he := covariantTensorDerivativeOnFields_eq D hT hO (hCons hZ hV) hy
    rw [hPoint] at he
    simp only [covariantTensorDerivativeOnFields, Fin.cons_zero, Fin.cons_succ] at he
    exact sub_eq_iff_eq_add.mp he
  have hzero {r : ℕ} {T : CovariantTensorEvaluation n M r}
      (hT : IsSmoothCovariantTensor T) (v : Fin r → TangentSpace (𝓡 n) x)
      (i : Fin r) (hi : v i = 0) : T x v = 0 := by
    obtain ⟨A, hA⟩ := hT.1 x
    rw [hA]
    exact A.map_coord_zero i hi
  let K := D.covariantTensorDerivative S
  have hK : IsSmoothCovariantTensor K := isSmoothCovariantTensor_covariantTensorDerivative D hS
  have hKzero (a : TangentSpace (𝓡 n) x) (i : Fin k) :
      K x (Fin.cons a (Function.update (fun j ↦ W j x) i 0)) = 0 := by
    apply hzero hK _ i.succ
    simp only [Fin.cons_succ, Function.update_self]
  let f := fun y ↦ S y (fun i ↦ W i y)
  have hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O := hS.2 O hO W hWO
  have hdfx (a : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) f x a = K x (Fin.cons a (fun i ↦ W i x)) := by
    have he := hDiff hS (hE a) hWO hxO
    simp only [FiberBundle.extend_apply_self] at he
    have hs : (∑ i, S x (Function.update (fun j ↦ W j x) i
        (D.connection (W i) x a))) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ hker i _
    rw [hs] at he
    simpa only [add_zero, K, f] using! he
  have hsecond (a : TangentSpace (𝓡 n) x) :
      0 ≤ D.iteratedCovariantTensorDerivative S 2 x
        (Fin.cons a (Fin.cons a (fun i ↦ W i x))) := by
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    have hY : Smooth Y := hE a
    let C (i : Fin k) := fun y ↦ D.connection (W i) y (Y y)
    have hC (i : Fin k) : Smooth (C i) := by
      intro y hy
      apply ContMDiffAt.contMDiffWithinAt
      apply contMDiffAt_section_of_metric_pairings g (C i)
      intro b
      let q := trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) y
      have hyq : y ∈ O ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
      exact (contMDiffOn_connection_pairing D (hO.inter q.open_baseSet)
        (hY.mono inter_subset_left) ((hWO i).mono inter_subset_left)
        ((contMDiffOn_extend_baseSet b).mono inter_subset_right)).contMDiffAt
          ((hO.inter q.open_baseSet).mem_nhds hyq)
    have hCx (i : Fin k) : C i x = 0 := by simp only [C, hDW, zero_apply]
    let p := fun y ↦ K y (Fin.cons (Y y) (fun i ↦ W i y))
    let q (i : Fin k) := fun y ↦ S y (Function.update (fun j ↦ W j y) i (C i y))
    have hp : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ p O := by
      simpa only [hPoint] using hK.2 O hO (Fin.cons Y W) (hCons hY hWO)
    have hq (i : Fin k) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q i) O := by
      simpa only [hPointUpdate] using
        hS.2 O hO (Function.update W i (C i)) (hUpdate hWO (hC i) i)
    have hfirst : (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) =ᶠ[𝓝 x] (p + ∑ i, q i) := by
      filter_upwards [hO.mem_nhds hxO] with y hy
      have he := hDiff hS hY hWO hy
      simpa only [Pi.add_apply, Finset.sum_apply, f, K, C, p, q] using! he
    have hdp : mvfderiv (𝓡 n) p x (Y x) =
        D.covariantTensorDerivative K x
          (Fin.cons (Y x) (Fin.cons (Y x) (fun i ↦ W i x))) +
        K x (Fin.cons (D.connection Y x (Y x)) (fun i ↦ W i x)) := by
      have he := hDiff hK hY (hCons hY hWO) hxO
      simp only [hPoint, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.update_cons_zero, ← Fin.cons_update] at he
      have hs : (∑ i, K x (Fin.cons (Y x) (Function.update (fun j ↦ W j x) i
          (D.connection (W i) x (Y x))))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simpa only [hDW, zero_apply] using hKzero (Y x) i
      simpa only [hs, add_zero, p] using! he
    have hdq (i : Fin k) : mvfderiv (𝓡 n) (q i) x (Y x) = 0 := by
      have he := hDiff hS hY (hUpdate hWO (hC i) i) hxO
      simp only [hPointUpdate, hCx] at he
      have hs (j : Fin k) (z : TangentSpace (𝓡 n) x) :
          S x (Function.update (Function.update (fun r ↦ W r x) i 0) j z) = 0 := by
        by_cases h : j = i
        · subst j
          simpa only [Function.update_idem] using hker i z
        · apply hzero hS _ i
          simp only [Function.update_of_ne (Ne.symm h), Function.update_self]
      have hsum : (∑ j, S x
          (Function.update (Function.update (fun r ↦ W r x) i 0) j
            (D.connection (Function.update W i (C i) j) x (Y x)))) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ hs j _
      simpa only [K, hKzero, hsum, add_zero, q] using! he
    have hpD := (hp.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)
    have hqD (i : Fin k) := ((hq i).contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt
      (by simp)
    have hqsumD : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (∑ i, q i) x :=
      MDifferentiableAt.sum (fun i _ ↦ hqD i)
    have hsumDeriv (w : TangentSpace (𝓡 n) x) :
        mvfderiv (𝓡 n) (∑ i, q i) x w = ∑ i, mvfderiv (𝓡 n) (q i) x w := by
      have he := (HasMFDerivAt.sum (t := (Finset.univ : Finset (Fin k)))
        (fun i _ ↦ (hqD i).hasMFDerivAt)).mfderiv
      change ((mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (∑ i, q i) x :
        TangentSpace (𝓡 n) x →L[ℝ] ℝ) w) =
        ∑ i, ((mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (q i) x :
          TangentSpace (𝓡 n) x →L[ℝ] ℝ) w)
      simpa only [sum_apply] using!
        congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ ↦ L w) he
    have hdd : mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (Y x) =
        D.covariantTensorDerivative K x
          (Fin.cons (Y x) (Fin.cons (Y x) (fun i ↦ W i x))) +
        K x (Fin.cons (D.connection Y x (Y x)) (fun i ↦ W i x)) := by
      have he : mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x =
          mvfderiv (𝓡 n) (p + ∑ i, q i) x := hfirst.mfderiv_eq
      rw [he, mvfderiv_add hpD hqsumD]
      simp only [add_apply, hdp, hsumDeriv, hdq, Finset.sum_const_zero, add_zero]
    have hh : D.hessian f x a a = D.iteratedCovariantTensorDerivative S 2 x
        (Fin.cons a (Fin.cons a (fun i ↦ W i x))) := by
      change mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (Y x) -
        mvfderiv (𝓡 n) f x (D.connection Y x (Y x)) = _
      rw [hdd, hdfx, add_sub_cancel_right]
      simp only [Y, FiberBundle.extend_apply_self,
        LeviCivitaData.iteratedCovariantTensorDerivative, K]
    rw [← hh]
    exact D.hessian_nonneg_of_isLocalMinAt (hf.contMDiffAt (hO.mem_nhds hxO)) hmin a
  exact Finset.sum_nonneg fun i _ ↦ hsecond (g.orthonormalBasis x i)

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem sectional_null_insertions
    {S : CovariantTensorEvaluation n M 4} (hS : IsSmoothCovariantTensor S)
    {x : M} (hpair : ∀ a b c d : TangentSpace (𝓡 n) x,
      S x ![a, b, c, d] = S x ![c, d, a, b])
    (hpos : ∀ a b : TangentSpace (𝓡 n) x, 0 ≤ S x ![a, b, a, b])
    (u v : TangentSpace (𝓡 n) x) (hnull : S x ![u, v, u, v] = 0) :
    ∀ i z, S x (Function.update ![u, v, u, v] i z) = 0 := by
  classical
  obtain ⟨A, hA⟩ := hS.1 x
  have hu0 (a b c d z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b, c, d] 0 z = ![z, b, c, d] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu1 (a b c d z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b, c, d] 1 z = ![a, z, c, d] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu2 (a b c d z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b, c, d] 2 z = ![a, b, z, d] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu3 (a b c d z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b, c, d] 3 z = ![a, b, c, z] := by
    funext i
    fin_cases i <;> simp [Function.update]
  let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
    { toFun := fun a ↦ A.toLinearMap ![a, v, 0, v] 2
      map_add' := by
        intro a b
        ext c
        simpa only [LinearMap.add_apply, MultilinearMap.toLinearMap_apply, hu2, hu0] using
          A.map_update_add ![0, v, c, v] 0 a b
      map_smul' := by
        intro s a
        ext b
        simpa only [LinearMap.smul_apply, RingHom.id_apply,
          MultilinearMap.toLinearMap_apply, hu2, hu0] using
          A.map_update_smul ![0, v, b, v] 0 s a }
  have hB (a b : TangentSpace (𝓡 n) x) : B a b = S x ![a, v, b, v] := by
    change A (Function.update ![a, v, 0, v] 2 b) = _
    rw [hu2]
    exact (hA _).symm
  have hBsymm : B.IsSymm := ⟨fun a b ↦ by simpa only [hB] using hpair a v b v⟩
  have hBu : B u = 0 := LinearMap.mem_ker.mp
    ((B.apply_apply_same_eq_zero_iff (fun a ↦ by simpa only [hB] using hpos a v)
      (LinearMap.BilinForm.isSymm_iff.mp hBsymm)).mp (by simpa only [hB] using hnull))
  have hBL (z : TangentSpace (𝓡 n) x) : S x ![u, v, z, v] = 0 := by
    rw [← hB, hBu]
    rfl
  have hBR (z : TangentSpace (𝓡 n) x) : S x ![z, v, u, v] = 0 :=
    (hpair z v u v).trans (hBL z)
  let C : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
    { toFun := fun a ↦ A.toLinearMap ![u, a, u, 0] 3
      map_add' := by
        intro a b
        ext c
        simpa only [LinearMap.add_apply, MultilinearMap.toLinearMap_apply, hu3, hu1] using
          A.map_update_add ![u, 0, u, c] 1 a b
      map_smul' := by
        intro s a
        ext b
        simpa only [LinearMap.smul_apply, RingHom.id_apply,
          MultilinearMap.toLinearMap_apply, hu3, hu1] using
          A.map_update_smul ![u, 0, u, b] 1 s a }
  have hC (a b : TangentSpace (𝓡 n) x) : C a b = S x ![u, a, u, b] := by
    change A (Function.update ![u, a, u, 0] 3 b) = _
    rw [hu3]
    exact (hA _).symm
  have hCsymm : C.IsSymm := ⟨fun a b ↦ by simpa only [hC] using hpair u a u b⟩
  have hCv : C v = 0 := LinearMap.mem_ker.mp
    ((C.apply_apply_same_eq_zero_iff (fun a ↦ by simpa only [hC] using hpos u a)
      (LinearMap.BilinForm.isSymm_iff.mp hCsymm)).mp (by simpa only [hC] using hnull))
  have hCL (z : TangentSpace (𝓡 n) x) : S x ![u, v, u, z] = 0 := by
    rw [← hC, hCv]
    rfl
  have hCR (z : TangentSpace (𝓡 n) x) : S x ![u, z, u, v] = 0 :=
    (hpair u z u v).trans (hCL z)
  intro i z
  fin_cases i
  · change S x (Function.update ![u, v, u, v] 0 z) = 0
    simpa only [hu0] using hBR z
  · change S x (Function.update ![u, v, u, v] 1 z) = 0
    simpa only [hu1] using hCR z
  · change S x (Function.update ![u, v, u, v] 2 z) = 0
    simpa only [hu2] using hBL z
  · change S x (Function.update ![u, v, u, v] 3 z) = 0
    simpa only [hu3] using hCL z

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem tensorLaplacian_nonneg_at_sectional_null (D : LeviCivitaData g)
    {S : CovariantTensorEvaluation n M 4} (hS : IsSmoothCovariantTensor S)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hpair : ∀ a b c d : TangentSpace (𝓡 n) x,
      S x ![a, b, c, d] = S x ![c, d, a, b])
    (hpos : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      0 ≤ S y ![a, b, a, b])
    (u v : TangentSpace (𝓡 n) x) (hnull : S x ![u, v, u, v] = 0) :
    0 ≤ D.tensorLaplacian S x ![u, v, u, v] := by
  classical
  have hker := sectional_null_insertions hS hpair (hpos x hx) u v hnull
  obtain ⟨V, X, hV, hxV, hX, hXu, hDX⟩ := exists_local_field_connection_zero D x u
  obtain ⟨L, Y, hL, hxL, hY, hYv, hDY⟩ := exists_local_field_connection_zero D x v
  let O := (U ∩ V) ∩ L
  have hO : IsOpen O := (hU.inter hV).inter hL
  have hxO : x ∈ O := ⟨⟨hx, hxV⟩, hxL⟩
  let W : Fin 4 → (y : M) → TangentSpace (𝓡 n) y := ![X, Y, X, Y]
  have hPoint (y : M) : (fun i ↦ W i y) = ![X y, Y y, X y, Y y] := by
    funext i
    fin_cases i <;> rfl
  have hW : ∀ i, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (W i)) O := by
    intro i
    fin_cases i
    · exact hX.mono (fun _ hy ↦ hy.1.2)
    · exact hY.mono inter_subset_right
    · exact hX.mono (fun _ hy ↦ hy.1.2)
    · exact hY.mono inter_subset_right
  have hDW (i : Fin 4) : D.connection (W i) x = 0 := by
    fin_cases i
    · exact hDX
    · exact hDY
    · exact hDX
    · exact hDY
  have hkerW (i : Fin 4) (z : TangentSpace (𝓡 n) x) :
      S x (Function.update (fun j ↦ W j x) i z) = 0 := by
    simpa only [hPoint, hXu, hYv] using hker i z
  have hmin : IsLocalMin (fun y ↦ S y (fun i ↦ W i y)) x := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    change S x (fun i ↦ W i x) ≤ S y (fun i ↦ W i y)
    rw [hPoint, hPoint, hXu, hYv, hnull]
    exact hpos y hy.1.1 (X y) (Y y)
  simpa only [hPoint, hXu, hYv] using
    local_null_fields_diffusion D hS hO hxO W hW hDW hkerW hmin

end PoincareConjecture.RicciFlowAnalysis
