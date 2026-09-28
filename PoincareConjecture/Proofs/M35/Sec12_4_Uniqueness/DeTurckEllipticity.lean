import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.DeTurckEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem metric_basis_inner_self (g : RiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1
  rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).orthonormal.norm_eq_one, one_pow]

private theorem covector_sq_le_metric_trace (h : RiemannianMetric n M) (x : M)
    (L : TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ) (v : TangentSpace (𝓡 n) x) :
    L v ^ 2 ≤ h.inner x v v *
      ∑ i, L (h.orthonormalBasis x i) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e := h.orthonormalBasis x
  have hL : L v = ∑ i, e.repr v i * L (e i) := by
    calc
      L v = L (∑ i, e.repr v i • e i) := congrArg L (e.sum_repr v).symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have hparseval : (∑ i, (e.repr v i) ^ 2) = h.inner x v v := by
    calc
      _ = ∑ i, ‖inner ℝ (e i) v‖ ^ 2 := by
        simp only [e.repr_apply_apply, Real.norm_eq_abs, sq_abs]
      _ = ‖v‖ ^ 2 := e.sum_sq_norm_inner_right v
      _ = _ := (real_inner_self_eq_norm_sq v).symm
  rw [hL]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => e.repr v i) (fun i => L (e i))).trans_eq (by rw [hparseval])

theorem covector_trace_le_of_metric_le (g h : RiemannianMetric n M) (x : M)
    {C : ℝ} (hdom : ∀ v, h.inner x v v ≤ C * g.inner x v v)
    (L : TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ) :
    (∑ i, L (g.orthonormalBasis x i) ^ 2) ≤
      (n : ℝ) * C * ∑ i, L (h.orthonormalBasis x i) ^ 2 := by
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      L (g.orthonormalBasis x i) ^ 2 ≤ C * ∑ j, L (h.orthonormalBasis x j) ^ 2 := by
    have hb : h.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) ≤ C := by
      simpa only [metric_basis_inner_self, mul_one] using hdom (g.orthonormalBasis x i)
    exact (covector_sq_le_metric_trace h x L _).trans
      (mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        C * ∑ j, L (h.orthonormalBasis x j) ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp [hdim, mul_assoc]

theorem fixed_tensorNorm_sq_first (g : RiemannianMetric n M) {r : ℕ}
    (A : CovariantTensorEvaluation n M (r + 1)) (x : M) :
    (g.tensorNorm A x) ^ 2 =
      ∑ i, ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        A x (Fin.cons (g.orthonormalBasis x i)
          (fun j => g.orthonormalBasis x (a j))) ^ 2 := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let f (a : Fin (r + 1) → Fin d) := (A x (fun j => b (a j))) ^ 2
  change (Real.sqrt (∑ a : Fin (r + 1) → Fin d, f a)) ^ 2 = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  let e := Fin.consEquiv (fun _ : Fin (r + 1) => Fin d)
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  change (A x (fun j => b ((Fin.cons i a : Fin (r + 1) → Fin d) j))) ^ 2 = _
  have he : (fun j => b ((Fin.cons i a : Fin (r + 1) → Fin d) j)) =
      (Fin.cons (b i) (fun j => b (a j)) : Fin (r + 1) → TangentSpace (𝓡 n) x) :=
    Fin.comp_cons b i a
  rw [he]

theorem tensor_first_slot_trace_coercive (g h : RiemannianMetric n M) {r : ℕ}
    {A : CovariantTensorEvaluation n M (r + 1)} (hA : IsSmoothCovariantTensor A)
    (x : M) {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ v, h.inner x v v ≤ C * g.inner x v v) :
    ((n : ℝ) * C + 1)⁻¹ * (g.tensorNorm A x) ^ 2 ≤
      ∑ i, ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        A x (Fin.cons (h.orthonormalBasis x i)
          (fun j => g.orthonormalBasis x (a j))) ^ 2 := by
  obtain ⟨Q, hQ⟩ := hA.1 x
  have htrace (a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      (∑ i, A x (Fin.cons (g.orthonormalBasis x i)
        (fun j => g.orthonormalBasis x (a j))) ^ 2) ≤
      (n : ℝ) * C * ∑ i, A x (Fin.cons (h.orthonormalBasis x i)
        (fun j => g.orthonormalBasis x (a j))) ^ 2 := by
    let w := fun j => g.orthonormalBasis x (a j)
    let L : TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ := {
      toFun := fun v => A x (Fin.cons v w)
      map_add' := fun u v => by simp only [hQ]; exact Q.cons_add w u v
      map_smul' := fun c v => by simp only [hQ]; exact Q.cons_smul w c v }
    exact covector_trace_le_of_metric_le g h x hdom L
  let E := ∑ i,
    ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      A x (Fin.cons (h.orthonormalBasis x i)
        (fun j => g.orthonormalBasis x (a j))) ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : (g.tensorNorm A x) ^ 2 ≤ (n : ℝ) * C * E := by
    rw [fixed_tensorNorm_sq_first, Finset.sum_comm]
    calc
      _ ≤ ∑ a : Fin r → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (n : ℝ) * C * ∑ i, A x (Fin.cons (h.orthonormalBasis x i)
            (fun j => g.orthonormalBasis x (a j))) ^ 2 :=
        Finset.sum_le_sum fun a _ => htrace a
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  have hden : 0 < (n : ℝ) * C + 1 := by positivity
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith

end PoincareConjecture.M35.Uniqueness
