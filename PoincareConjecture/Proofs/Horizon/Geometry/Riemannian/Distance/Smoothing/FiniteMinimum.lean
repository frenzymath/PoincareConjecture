import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum.Finite
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Minimum








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]


theorem contMDiffAt_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x := by
  induction k with
  | zero => exact hf 0
  | succ k ih =>
    exact contMDiffAt_regularizedMin δ hδ (hf 0)
      (ih (fun i => f i.succ) (fun i => hf i.succ))



theorem mvfderiv_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x v =
      ∑ i, Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i *
        mvfderiv (𝓡 n) (f i) x v := by
  induction k with
  | zero => simp [Poincare.finiteRegularizedMin, Poincare.finiteRegularizedMinWeight]
  | succ k ih =>
    change mvfderiv (𝓡 n)
      (fun y => Poincare.regularizedMin δ hδ (f 0 y)
        (Poincare.finiteRegularizedMin δ hδ k (fun i => f i.succ y))) x v = _
    rw [mvfderiv_regularizedMin δ hδ ((hf 0).mdifferentiableAt (by simp))
      ((contMDiffAt_finiteRegularizedMin δ hδ k (fun i => f i.succ)
        (fun i => hf i.succ)).mdifferentiableAt (by simp)),
      ih (fun i => f i.succ) (fun i => hf i.succ)]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Poincare.finiteRegularizedMinWeight, Fin.cases_zero, Fin.cases_succ,
      Fin.tail_def]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]

private theorem weighted_sum_le_of_active {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) {B : ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, w i ≠ 0 → a i ≤ B) : ∑ i, w i * a i ≤ B := by
  calc
    _ ≤ ∑ i, w i * B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hwi : w i = 0
      · simp [hwi]
      · exact mul_le_mul_of_nonneg_left (ha i hwi) (hw i)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

private theorem le_weighted_sum_of_active {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) {B : ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∀ i, w i ≠ 0 → B ≤ a i) : B ≤ ∑ i, w i * a i := by
  calc
    B = ∑ i, w i * B := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hwi : w i = 0
      · simp [hwi]
      · exact mul_le_mul_of_nonneg_left (ha i hwi) (hw i)


theorem mvfderiv_finiteRegularizedMin_le_of_active (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (v : TangentSpace (𝓡 n) x) {B : ℝ}
    (hB : ∀ i, Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i ≠ 0 →
      mvfderiv (𝓡 n) (f i) x v ≤ B) :
    mvfderiv (𝓡 n) (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x v ≤ B := by
  rw [mvfderiv_finiteRegularizedMin δ hδ k f hf]
  exact weighted_sum_le_of_active _ _ (Poincare.finiteRegularizedMinWeight_nonneg δ hδ k _)
    (Poincare.sum_finiteRegularizedMinWeight δ hδ k _) hB


theorem le_mvfderiv_finiteRegularizedMin_of_active (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (v : TangentSpace (𝓡 n) x) {B : ℝ}
    (hB : ∀ i, Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i ≠ 0 →
      B ≤ mvfderiv (𝓡 n) (f i) x v) :
    B ≤ mvfderiv (𝓡 n) (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x v := by
  rw [mvfderiv_finiteRegularizedMin δ hδ k f hf]
  exact le_weighted_sum_of_active _ _ (Poincare.finiteRegularizedMinWeight_nonneg δ hδ k _)
    (Poincare.sum_finiteRegularizedMinWeight δ hδ k _) hB


theorem contMDiffOn_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (f : Fin (k + 1) → M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) U := by
  intro x hx
  exact (contMDiffAt_finiteRegularizedMin δ hδ k f
    (fun i => (hf i x hx).contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt

namespace LeviCivitaData

variable [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}



theorem hessian_finiteRegularizedMin_le_weighted (D : LeviCivitaData g)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x v v ≤
      ∑ i, Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i *
        D.hessian (f i) x v v := by
  induction k with
  | zero => simp [Poincare.finiteRegularizedMin, Poincare.finiteRegularizedMinWeight]
  | succ k ih =>
    let t : M → ℝ := fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i.succ y)
    have ht : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ t x :=
      contMDiffAt_finiteRegularizedMin δ hδ k (fun i => f i.succ) (fun i => hf i.succ)
    let d := deriv (Poincare.regularizedAbs δ hδ) (f 0 x - t x)
    have hd := abs_le.mp (Poincare.abs_deriv_regularizedAbs_le_one δ hδ (f 0 x - t x))
    have hc := mul_nonneg
      (div_nonneg (Poincare.deriv2_regularizedAbs_nonneg δ hδ (f 0 x - t x))
        (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg (mvfderiv (𝓡 n) (f 0) x v - mvfderiv (𝓡 n) t x v))
    change D.hessian (fun y => Poincare.regularizedMin δ hδ (f 0 y) (t y)) x v v ≤ _
    calc
      _ ≤ ((1 - d) / 2) * D.hessian (f 0) x v v +
          ((1 + d) / 2) * D.hessian t x v v := by
        rw [D.hessian_regularizedMin δ hδ (hf 0) ht]
        dsimp only [d]
        nlinarith only [hc]
      _ ≤ ((1 - d) / 2) * D.hessian (f 0) x v v +
          ((1 + d) / 2) * (∑ i, Poincare.finiteRegularizedMinWeight δ hδ k
            (fun i => f i.succ x) i * D.hessian (f i.succ) x v v) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (ih (fun i => f i.succ) (fun i => hf i.succ))
          (show 0 ≤ (1 + d) / 2 by dsimp only [d]; linarith [hd.1]))
      _ = _ := by
        conv_rhs => rw [Fin.sum_univ_succ]
        simp only [Poincare.finiteRegularizedMinWeight, Fin.cases_zero, Fin.cases_succ,
          Fin.tail_def]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]



theorem hessian_finiteRegularizedMin_le_of_active (D : LeviCivitaData g)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (v : TangentSpace (𝓡 n) x) {H : ℝ}
    (hH : ∀ i, Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i ≠ 0 →
      D.hessian (f i) x v v ≤ H * g.inner x v v) :
    D.hessian (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x v v ≤
      H * g.inner x v v := by
  apply (D.hessian_finiteRegularizedMin_le_weighted δ hδ k f hf v).trans
  exact weighted_sum_le_of_active _ _ (Poincare.finiteRegularizedMinWeight_nonneg δ hδ k _)
    (Poincare.sum_finiteRegularizedMinWeight δ hδ k _) hH


theorem gradient_finiteRegularizedMin_norm_le_of_active (D : LeviCivitaData g)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ i, Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i ≠ 0 →
      Real.sqrt (g.inner x (D.gradient (f i) x) (D.gradient (f i) x)) ≤ L) :
    Real.sqrt (g.inner x
      (D.gradient (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x)
      (D.gradient (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x)) ≤ L := by
  apply (D.gradient_norm_le_iff _ x hL).mpr
  intro v
  have hi (i) (hwi : Poincare.finiteRegularizedMinWeight δ hδ k (fun i => f i x) i ≠ 0) :=
    (D.gradient_norm_le_iff (f i) x hL).mp (hbound i hwi) v
  apply abs_le.mpr
  exact ⟨le_mvfderiv_finiteRegularizedMin_of_active δ hδ k f hf v
      (fun i hwi => (abs_le.mp (hi i hwi)).1),
    mvfderiv_finiteRegularizedMin_le_of_active δ hδ k f hf v
      (fun i hwi => (abs_le.mp (hi i hwi)).2)⟩



theorem hessian_finiteRegularizedMin_le_of_value_gap (D : LeviCivitaData g)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    (v : TangentSpace (𝓡 n) x) {H : ℝ}
    (hH : ∀ i, f i x ≤ (⨅ j, f j x) + 2 * k * δ →
      D.hessian (f i) x v v ≤ H * g.inner x v v) :
    D.hessian (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x v v ≤
      H * g.inner x v v := by
  apply D.hessian_finiteRegularizedMin_le_of_active δ hδ k f hf v
  intro i hi
  apply hH i
  by_contra hgap
  exact hi (Poincare.finiteRegularizedMinWeight_eq_zero_of_iInf_gap δ hδ k
    (fun i => f i x) i (lt_of_not_ge hgap))



theorem gradient_finiteRegularizedMin_norm_le_of_value_gap (D : LeviCivitaData g)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (f : Fin (k + 1) → M → ℝ) {x : M}
    (hf : ∀ i, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) x)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ i, f i x ≤ (⨅ j, f j x) + 2 * k * δ →
      Real.sqrt (g.inner x (D.gradient (f i) x) (D.gradient (f i) x)) ≤ L) :
    Real.sqrt (g.inner x
      (D.gradient (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x)
      (D.gradient (fun y => Poincare.finiteRegularizedMin δ hδ k (fun i => f i y)) x)) ≤ L := by
  apply D.gradient_finiteRegularizedMin_norm_le_of_active δ hδ k f hf hL
  intro i hi
  apply hbound i
  by_contra hgap
  exact hi (Poincare.finiteRegularizedMinWeight_eq_zero_of_iInf_gap δ hδ k
    (fun i => f i x) i (lt_of_not_ge hgap))

end LeviCivitaData
end PoincareConjecture
