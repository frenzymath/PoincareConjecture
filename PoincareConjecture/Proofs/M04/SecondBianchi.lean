import PoincareConjecture.Proofs.M04.CurvatureSymmetries
import PoincareConjecture.Proofs.M04.RiemannRegularity
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure





set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem riemann_second_bianchi (D : LeviCivitaData g) (x : M)
    (a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] +
      D.covariantTensorDerivative D.riemannEvaluation x ![b, c, a, d, e] +
      D.covariantTensorDerivative D.riemannEvaluation x ![c, a, b, d, e] = 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let U := t.baseSet
  have hU : IsOpen U := t.open_baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt' x
  let V : Fin 3 → (y : M) → TangentSpace (𝓡 n) y :=
    ![FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) c]
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) d
  let A := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) e
  have hV (i : Fin 3) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V i)) U := by
    fin_cases i
    · exact contMDiffOn_extend_baseSet a
    · exact contMDiffOn_extend_baseSet b
    · exact contMDiffOn_extend_baseSet c
  have hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% W) U := contMDiffOn_extend_baseSet d
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U := contMDiffOn_extend_baseSet e
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  let B (i j : Fin 3) := VectorField.mlieBracket (𝓡 n) (V i) (V j)
  have hB (i j : Fin 3) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (B i j)) U := by
    intro y hy
    exact (((hV i y hy).contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (m := ⊤) (n := ⊤) ((hV j y hy).contMDiffAt (hU.mem_nhds hy))
      (by simp)).contMDiffWithinAt
  let G (i : Fin 3) := fun y ↦ D.connection A y (V i y)
  have hG (i : Fin 3) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (G i)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (G i)
    intro v
    let q := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing D (hU.inter q.open_baseSet)
      ((hV i).mono Set.inter_subset_left) (hA.mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)).contMDiffAt
        ((hU.inter q.open_baseSet).mem_nhds hyq)
  let H (i j : Fin 3) := fun y ↦ D.connection (G j) y (V i y)
  have hH (i j : Fin 3) (_hij : i ≠ j) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (H i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (H i j)
    intro v
    let q := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing D (hU.inter q.open_baseSet)
      ((hV i).mono Set.inter_subset_left) ((hG j).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)).contMDiffAt
        ((hU.inter q.open_baseSet).mem_nhds hyq)
  let K (i j : Fin 3) := fun y ↦ D.connection A y (B i j y)
  have hK (i j : Fin 3) (_hij : i ≠ j) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (K i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (K i j)
    intro v
    let q := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing D (hU.inter q.open_baseSet)
      ((hB i j).mono Set.inter_subset_left) (hA.mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)).contMDiffAt
        ((hU.inter q.open_baseSet).mem_nhds hyq)
  let L (i j : Fin 3) := fun y ↦ D.connection (V j) y (V i y)
  have hL (i j : Fin 3) (_hij : i ≠ j) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (L i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (L i j)
    intro v
    let q := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing D (hU.inter q.open_baseSet)
      ((hV i).mono Set.inter_subset_left) ((hV j).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)).contMDiffAt
        ((hU.inter q.open_baseSet).mem_nhds hyq)
  let C (i j : Fin 3) := D.curvatureOnFields (V i) (V j) A
  have hC (i j : Fin 3) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (C i j)) U :=
    contMDiffOn_curvatureOnFields D hU (hV i) (hV j) hA
  have hDsub {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% P) x)
      (hQ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Q) x) :
      D.connection (P - Q) x = D.connection P x - D.connection Q x := by
    have hn : D.connection (-Q) x = -D.connection Q x := by
      simpa only [neg_one_smul] using
        D.connection.isCovariantDerivativeOnUniv.smul_const (-1 : ℝ) hQ
    have ha := D.connection.isCovariantDerivativeOnUniv.add hP
      (mdifferentiableAt_neg_section hQ)
    rw [hn] at ha
    simpa only [sub_eq_add_neg] using ha
  have hDC (i j k : Fin 3) (hjk : j ≠ k) :
      D.connection (C j k) x (V i x) =
        D.connection (H j k) x (V i x) - D.connection (H k j) x (V i x) -
          D.connection (K j k) x (V i x) := by
    have h1 := ((hH j k hjk x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have h2 := ((hH k j hjk.symm x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have h3 := ((hK j k hjk x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    change D.connection ((H j k - H k j) - K j k) x (V i x) = _
    rw [hDsub (mdifferentiableAt_sub_section h1 h2) h3, hDsub h1 h2]
    rfl
  have hVAt (i : Fin 3) := (hV i x hx).contMDiffAt (hU.mem_nhds hx)
  have hmin : (minSmoothness ℝ 2 : ℕ∞ω) ≤ ∞ := by
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  have hJac : VectorField.mlieBracket (𝓡 n) (B 0 1) (V 2) x +
      VectorField.mlieBracket (𝓡 n) (B 1 2) (V 0) x +
      VectorField.mlieBracket (𝓡 n) (B 2 0) (V 1) x = 0 := by
    have hJ := VectorField.leibniz_identity_mlieBracket_apply
      ((hVAt 0).of_le hmin) ((hVAt 1).of_le hmin) ((hVAt 2).of_le hmin)
    rw [VectorField.mlieBracket_swap (V := V 0) (W := V 2)] at hJ
    have hn : VectorField.mlieBracket (𝓡 n) (V 1)
        (-VectorField.mlieBracket (𝓡 n) (V 2) (V 0)) x =
        -VectorField.mlieBracket (𝓡 n) (V 1) (B 2 0) x := by
      simpa only [neg_one_smul] using
        VectorField.mlieBracket_const_smul_right (V := V 1) (c := (-1 : ℝ))
          (((hB 2 0 x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    rw [hn] at hJ
    rw [VectorField.mlieBracket_swap_apply (V := B 1 2) (W := V 0),
      VectorField.mlieBracket_swap_apply (V := B 2 0) (W := V 1)]
    change VectorField.mlieBracket (𝓡 n) (V 0) (B 1 2) x =
      VectorField.mlieBracket (𝓡 n) (B 0 1) (V 2) x -
        VectorField.mlieBracket (𝓡 n) (V 1) (B 2 0) x at hJ
    rw [hJ]
    abel
  have hOp :
      (D.connection (C 1 2) x (V 0 x) - D.curvatureOnFields (V 1) (V 2) (G 0) x) +
      (D.connection (C 2 0) x (V 1 x) - D.curvatureOnFields (V 2) (V 0) (G 1) x) +
      (D.connection (C 0 1) x (V 2 x) - D.curvatureOnFields (V 0) (V 1) (G 2) x) =
        D.curvatureOnFields (B 0 1) (V 2) A x +
          D.curvatureOnFields (B 1 2) (V 0) A x +
          D.curvatureOnFields (B 2 0) (V 1) A x := by
    calc
      _ = (D.curvatureOnFields (B 0 1) (V 2) A x +
          D.curvatureOnFields (B 1 2) (V 0) A x +
          D.curvatureOnFields (B 2 0) (V 1) A x) +
          D.connection A x (VectorField.mlieBracket (𝓡 n) (B 0 1) (V 2) x +
            VectorField.mlieBracket (𝓡 n) (B 1 2) (V 0) x +
            VectorField.mlieBracket (𝓡 n) (B 2 0) (V 1) x) := by
        rw [hDC 0 1 2 (by decide), hDC 1 2 0 (by decide), hDC 2 0 1 (by decide)]
        simp only [LeviCivitaData.curvatureOnFields, H, G, K, B, map_add]
        abel
      _ = _ := by rw [hJac, map_zero, add_zero]
  have hT (i j : Fin 3) : Set.EqOn (L i j - L j i) (B i j) U := by
    intro y hy
    exact connection_commutator D
      (((hV i y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
      (((hV j y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
  have hRsub (i j k : Fin 3) (hij : i ≠ j) :
      D.curvatureOnFields (L i j) (V k) A x - D.curvatureOnFields (L j i) (V k) A x =
        D.curvatureOnFields (B i j) (V k) A x := by
    have hn : D.curvatureOnFields (-(L j i)) (V k) A x =
        -D.curvatureOnFields (L j i) (V k) A x := by
      simpa only [Pi.smul_def', Pi.neg_def, neg_one_smul] using curvatureOnFields_smul_left D hU
        (f := fun _ ↦ (-1 : ℝ)) contMDiffOn_const
        (hL j i hij.symm) (hV k) hA hx
    have ha := curvatureOnFields_add_left D hU (hL i j hij)
      (hL j i hij.symm).neg_section (hV k) hA hx
    rw [hn] at ha
    have he := curvatureOnFields_congr D hU
      ((hL i j hij).sub_section (hL j i hij.symm)) (hV k) hA
      (hB i j) (hV k) hA (hT i j) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hx
    simpa only [sub_eq_add_neg] using ha.symm.trans he
  have hInput :
      (D.curvatureOnFields (L 0 1) (V 2) A x + D.curvatureOnFields (V 1) (L 0 2) A x) +
      (D.curvatureOnFields (L 1 2) (V 0) A x + D.curvatureOnFields (V 2) (L 1 0) A x) +
      (D.curvatureOnFields (L 2 0) (V 1) A x + D.curvatureOnFields (V 0) (L 2 1) A x) =
        D.curvatureOnFields (B 0 1) (V 2) A x +
          D.curvatureOnFields (B 1 2) (V 0) A x +
          D.curvatureOnFields (B 2 0) (V 1) A x := by
    rw [curvatureOnFields_swap D (L 0 2) (V 1) A x,
      curvatureOnFields_swap D (L 1 0) (V 2) A x,
      curvatureOnFields_swap D (L 2 1) (V 0) A x,
      ← hRsub 0 1 2 (by decide), ← hRsub 1 2 0 (by decide), ← hRsub 2 0 1 (by decide)]
    abel
  let Q (i j k : Fin 3) := D.connection (C j k) x (V i x) -
    D.curvatureOnFields (L i j) (V k) A x - D.curvatureOnFields (V j) (L i k) A x -
    D.curvatureOnFields (V j) (V k) (G i) x
  have hQ : Q 0 1 2 + Q 1 2 0 + Q 2 0 1 = 0 := by
    calc
      _ = ((D.connection (C 1 2) x (V 0 x) - D.curvatureOnFields (V 1) (V 2) (G 0) x) +
          (D.connection (C 2 0) x (V 1 x) - D.curvatureOnFields (V 2) (V 0) (G 1) x) +
          (D.connection (C 0 1) x (V 2 x) - D.curvatureOnFields (V 0) (V 1) (G 2) x)) -
          ((D.curvatureOnFields (L 0 1) (V 2) A x + D.curvatureOnFields (V 1) (L 0 2) A x) +
          (D.curvatureOnFields (L 1 2) (V 0) A x + D.curvatureOnFields (V 2) (L 1 0) A x) +
          (D.curvatureOnFields (L 2 0) (V 1) A x + D.curvatureOnFields (V 0) (L 2 1) A x)) := by
        dsimp only [Q]
        abel
      _ = 0 := by rw [hOp, hInput, sub_self]
  have hR {X Y Z : (y : M) → TangentSpace (𝓡 n) y}
      (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
      (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
      (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
      {y : M} (hy : y ∈ U) (w : TangentSpace (𝓡 n) y) :
      D.curvatureTensor y (X y) (Y y) w (Z y) =
        g.inner y (D.curvatureOnFields X Y Z y) w := by
    rw [LeviCivitaData.curvatureTensor, ← curvatureOnFields_eq_curvature D hU hX hY hZ hy]
  have hDer (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) :
      D.covariantTensorDerivative D.riemannEvaluation x
        ![V i x, V j x, V k x, W x, A x] = g.inner x (Q i j k) (W x) := by
    let Z : Fin 5 → (y : M) → TangentSpace (𝓡 n) y := ![V i, V j, V k, W, A]
    have hZ (l : Fin 5) : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Z l)) U := by
      fin_cases l
      · exact hV i
      · exact hV j
      · exact hV k
      · exact hW
      · exact hA
    have he := covariantTensorDerivativeOnFields_eq D
      (isSmoothCovariantTensor_riemannEvaluation D) hU hZ hx
    have htup : (fun l ↦ Z l x) = ![V i x, V j x, V k x, W x, A x] := by
      funext l
      fin_cases l <;> rfl
    rw [htup] at he
    rw [← he]
    have hE : (fun y ↦ D.curvatureTensor y (V j y) (V k y) (W y) (A y)) =ᶠ[𝓝 x]
        (fun y ↦ g.inner y (C j k y) (W y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hR (hV j) (hV k) hA hy (W y)
    have hDE := hE.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))
    simp only [covariantTensorDerivativeOnFields, Fin.sum_univ_succ]
    change mvfderiv (𝓡 n)
        (fun y ↦ D.curvatureTensor y (V j y) (V k y) (W y) (A y)) x (V i x) -
      (D.curvatureTensor x (L i j x) (V k x) (W x) (A x) +
        (D.curvatureTensor x (V j x) (L i k x) (W x) (A x) +
          (D.curvatureTensor x (V j x) (V k x) (D.connection W x (V i x)) (A x) +
            (D.curvatureTensor x (V j x) (V k x) (W x) (G i x) + 0)))) = _
    simp only [mvfderiv]
    erw [hDE]
    erw [metric_derivative_pairing D (V i)
      (((hC j k x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hW x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))]
    rw [hR (hL i j hij) (hV k) hA hx (W x), hR (hV j) (hL i k hik) hA hx (W x),
      hR (hV j) (hV k) hA hx (D.connection W x (V i x)),
      hR (hV j) (hV k) (hG i) hx (W x)]
    simp only [Q, C, map_sub, sub_apply]
    ring
  have hFinal :
      D.covariantTensorDerivative D.riemannEvaluation x ![V 0 x, V 1 x, V 2 x, W x, A x] +
      D.covariantTensorDerivative D.riemannEvaluation x ![V 1 x, V 2 x, V 0 x, W x, A x] +
      D.covariantTensorDerivative D.riemannEvaluation x ![V 2 x, V 0 x, V 1 x, W x, A x] = 0 := by
    rw [hDer 0 1 2 (by decide) (by decide), hDer 1 2 0 (by decide) (by decide),
      hDer 2 0 1 (by decide) (by decide)]
    simpa only [map_add, add_apply, map_zero, zero_apply] using
      congrArg (fun v ↦ g.inner x v (W x)) hQ
  simpa [V, W, A] using hFinal

end PoincareConjecture.M04

