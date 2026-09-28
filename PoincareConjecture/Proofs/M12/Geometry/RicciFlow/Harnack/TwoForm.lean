import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Harnack.TensorContractions









open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I]


lemma skew_contraction_half_wedge (A : I → I → ℝ)
    (hA : ∀ i j, A i j = -A j i) (V W : I → ℝ) :
    (∑ i, ∑ j, A i j * ((V i * W j - W i * V j) / 2)) =
      ∑ i, ∑ j, A i j * V i * W j := by
  have hswap : (∑ i, ∑ j, A i j * W i * V j) =
      -(∑ i, ∑ j, A i j * V i * W j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j i]
    ring
  calc
    _ = ((∑ i, ∑ j, A i j * V i * W j) -
        (∑ i, ∑ j, A i j * W i * V j)) / 2 := by
      simp only [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hswap]; ring

private lemma sum_four_swap_pairs (f : I → I → I → I → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_comm_cycle



lemma curvature_contraction_half_wedge (Rm : I → I → I → I → ℝ)
    (hfirst : ∀ i j k l, Rm i j k l = -Rm j i k l)
    (hlast : ∀ i j k l, Rm i j k l = -Rm i j l k) (V W : I → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      Rm i j k l * ((V i * W j - W i * V j) / 2) *
        ((V k * W l - W k * V l) / 2)) =
      ∑ i, ∑ j, ∑ k, ∑ l, Rm i j k l * V i * W j * V k * W l := by
  have hlastContract (i j : I) :
      (∑ k, ∑ l,
        Rm i j k l * ((V i * W j - W i * V j) / 2) *
          ((V k * W l - W k * V l) / 2)) =
        ∑ k, ∑ l, Rm i j k l * ((V i * W j - W i * V j) / 2) * V k * W l := by
    apply skew_contraction_half_wedge
    intro k l
    rw [hlast i j k l]
    ring
  have hfirstContract (k l : I) :
      (∑ i, ∑ j, Rm i j k l * ((V i * W j - W i * V j) / 2) * V k * W l) =
        ∑ i, ∑ j, Rm i j k l * V i * W j * V k * W l := by
    simpa only [Finset.sum_mul] using
      congrArg (fun z : ℝ => z * V k * W l)
        (skew_contraction_half_wedge (fun i j => Rm i j k l)
          (fun i j => hfirst i j k l) V W)
  simp_rw [hlastContract]
  rw [sum_four_swap_pairs]
  simp_rw [hfirstContract]
  exact (sum_four_swap_pairs _).symm

variable [DecidableEq I]



lemma curvature_contraction_half_wedge_trace (Rm : I → I → I → I → ℝ)
    (Ric : I → I → ℝ)
    (hfirst : ∀ i j k l, Rm i j k l = -Rm j i k l)
    (hlast : ∀ i j k l, Rm i j k l = -Rm i j l k)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l) (V : I → ℝ) :
    (∑ a, ∑ i, ∑ j, ∑ k, ∑ l,
      Rm i j k l * ((V i * (if j = a then 1 else 0) -
        (if i = a then 1 else 0) * V j) / 2) *
        ((V k * (if l = a then 1 else 0) -
          (if k = a then 1 else 0) * V l) / 2)) =
      ∑ i, ∑ k, Ric i k * V i * V k := by
  have hcontract (a : I) :
      (∑ i, ∑ j, ∑ k, ∑ l,
        Rm i j k l * ((V i * (if j = a then 1 else 0) -
          (if i = a then 1 else 0) * V j) / 2) *
          ((V k * (if l = a then 1 else 0) -
            (if k = a then 1 else 0) * V l) / 2)) =
        ∑ i, ∑ k, Rm i a k a * V i * V k := by
    rw [curvature_contraction_half_wedge Rm hfirst hlast V
      (fun i => if i = a then 1 else 0)]
    simp [mul_ite, ite_mul, Finset.sum_ite_irrel]
  simp_rw [hcontract]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, ← Finset.sum_mul, hRic]



lemma mixed_contraction_half_wedge_trace (P : I → I → I → ℝ)
    (hP : ∀ i j k, P i j k = -P j i k) (V : I → ℝ) :
    (∑ a, ∑ i, ∑ j, ∑ k,
      P i j k * ((V i * (if j = a then 1 else 0) -
        (if i = a then 1 else 0) * V j) / 2) *
        (if k = a then 1 else 0)) =
      ∑ i, (∑ a, P i a a) * V i := by
  have hcontract (a : I) :
      (∑ i, ∑ j, ∑ k,
        P i j k * ((V i * (if j = a then 1 else 0) -
          (if i = a then 1 else 0) * V j) / 2) *
          (if k = a then 1 else 0)) = ∑ i, P i a a * V i := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simpa [mul_ite] using skew_contraction_half_wedge (fun i j => P i j a)
      (fun i j => hP i j a) V (fun i => if i = a then 1 else 0)
  simp_rw [hcontract]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]



lemma matrix_quadratic_half_wedge_trace (S : I → I → ℝ)
    (P : I → I → I → ℝ) (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hP : ∀ i j k, P i j k = -P j i k)
    (hfirst : ∀ i j k l, Rm i j k l = -Rm j i k l)
    (hlast : ∀ i j k l, Rm i j k l = -Rm i j l k)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l) (V : I → ℝ) :
    let e : I → I → ℝ := fun a i => if i = a then 1 else 0
    let U : I → I → I → ℝ := fun a i j => (V i * e a j - e a i * V j) / 2
    (∑ a, ((∑ i, ∑ j, S i j * e a i * e a j) +
      2 * (∑ i, ∑ j, ∑ k, P i j k * U a i j * e a k) +
      (∑ i, ∑ j, ∑ k, ∑ l, Rm i j k l * U a i j * U a k l))) =
      (∑ a, S a a) + 2 * (∑ i, (∑ a, P i a a) * V i) +
        (∑ i, ∑ k, Ric i k * V i * V k) := by
  dsimp only
  have hS (a : I) :
      (∑ i, ∑ j, S i j * (if i = a then 1 else 0) *
        (if j = a then 1 else 0)) = S a a := by
    simp [mul_ite]
  simp_rw [hS]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [mixed_contraction_half_wedge_trace P hP V,
    curvature_contraction_half_wedge_trace Rm Ric hfirst hlast hRic V]

end Poincare.RicciFlow.Harnack
