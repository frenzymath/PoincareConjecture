import PoincareConjecture.Proofs.M34.Mathlib.CapPersistenceFrameJets
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound










set_option autoImplicit false

open Filter
open scoped ContDiff BigOperators Topology
open Poincare.Analysis.Calculus





theorem norm_iteratedFDeriv_le_of_covariantArray
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (e : ι → E) (ell : ι → E →L[ℝ] ℝ)
    (hframe : ∀ v : E, ∑ i, ell i v • e i = v)
    (r N : ℕ) (x : E) (Γ : E → ι → ι → ι → ℝ)
    (T : (k : ℕ) → E → (Fin (r + k) → ι) → ℝ)
    (hΓs : ∀ a b d, ContDiffAt ℝ ∞ (fun y => Γ y a b d) x)
    (hTs : ∀ k ≤ N, ∀ a, ContDiffAt ℝ ∞ (fun y => T k y a) x)
    (hrec : ∀ k < N, ∀ a : Fin (r + (k + 1)) → ι,
      (fun y => T (k + 1) y a) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ (fun z => T k z (fun i => a i.succ)) y
          (e (a ⟨0, by omega⟩)) -
          ∑ i : Fin (r + k), ∑ d : ι,
            Γ y d (a ⟨0, by omega⟩) (a i.succ) *
              T k y (Function.update (fun l => a l.succ) i d)))
    {D L A : ℝ} (hD : 0 ≤ D) (hL₁ : 1 ≤ L) (hA : 0 ≤ A)
    (hL : (∑ i, ‖ContinuousLinearMap.smulRightL ℝ E ℝ (ell i)‖) *
      (1 + (r + N : ℕ) * (Fintype.card ι : ℝ) * (2 : ℝ) ^ N * D) ≤ L)
    (hΓ : ∀ j ≤ N, ∀ a b d,
      ‖iteratedFDeriv ℝ j (fun y => Γ y a b d) x‖ ≤ D)
    (hb : ∀ k ≤ N, ∀ a, |T k x a| ≤ A)
    (k j : ℕ) (hkj : k + j ≤ N) (a : Fin (r + k) → ι) :
    ‖iteratedFDeriv ℝ j (fun y => T k y a) x‖ ≤ L ^ j * A := by
  classical
  have hL₀ : 0 ≤ L := zero_le_one.trans hL₁
  induction j using Nat.strong_induction_on generalizing k with
  | h j ih =>
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul]
        using hb k (by simpa using hkj) a
    | succ j =>
      have hkN : k < N := by omega
      have hprev (l : ℕ) (hl : l ≤ j) (b : Fin (r + k) → ι) :
          ‖iteratedFDeriv ℝ l (fun y => T k y b) x‖ ≤ L ^ j * A := by
        exact (ih l (by omega) k (by omega) b).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL₁ hl) hA)
      let F := fun (v : ι) (i : Fin (r + k)) (d : ι) y =>
        Γ y d v (a i) * T k y (Function.update a i d)
      have hFs (v : ι) (i : Fin (r + k)) (d : ι) :
          ContDiffAt ℝ ∞ (F v i d) x :=
        (hΓs _ _ _).mul (hTs k (by omega) _)
      have hFb (v : ι) (i : Fin (r + k)) (d : ι) :
          ‖iteratedFDeriv ℝ j (F v i d) x‖ ≤ (2 : ℝ) ^ N * D * (L ^ j * A) := by
        have hm := norm_iteratedFDeriv_bilinear_le_of_jet_bounds
          (ContinuousLinearMap.mul ℝ ℝ) (hΓs d v (a i))
          (hTs k (by omega) (Function.update a i d)) j hD
          (fun l hl => hΓ l (by omega) d v (a i)) (fun l hl => hprev l hl _)
        simp only [ContinuousLinearMap.opNorm_mul, one_mul] at hm
        exact hm.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : j ≤ N)) hD)
          (mul_nonneg (pow_nonneg hL₀ _) hA))
      have hsum (v : ι) :
          ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ d, F v i d y) x‖ ≤
            (r + N : ℕ) * (Fintype.card ι : ℝ) *
              ((2 : ℝ) ^ N * D * (L ^ j * A)) := by
        calc
          _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => ∑ d, F v i d y) x‖ :=
            norm_iteratedFDeriv_sum_le_of_contDiffAt Finset.univ j
              (fun i _ => (ContDiffAt.sum fun d _ => hFs v i d).of_le
                (by exact_mod_cast le_top))
          _ ≤ ∑ i, ∑ d, ‖iteratedFDeriv ℝ j (F v i d) x‖ :=
            Finset.sum_le_sum fun i _ => norm_iteratedFDeriv_sum_le_of_contDiffAt
              Finset.univ j (fun d _ => (hFs v i d).of_le (by exact_mod_cast le_top))
          _ ≤ ∑ _i : Fin (r + k), ∑ _d : ι, (2 : ℝ) ^ N * D * (L ^ j * A) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun d _ => hFb v i d
          _ = (r + k : ℕ) * (Fintype.card ι : ℝ) *
              ((2 : ℝ) ^ N * D * (L ^ j * A)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast (by omega : r + k ≤ r + N)
      have hdir (v : ι) :
          ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (fun z => T k z a) y (e v)) x‖ ≤
            (1 + (r + N : ℕ) * (Fintype.card ι : ℝ) * (2 : ℝ) ^ N * D) *
              (L ^ j * A) := by
        have heq : (fun y => fderiv ℝ (fun z => T k z a) y (e v)) =ᶠ[𝓝 x]
            (fun y => T (k + 1) y (Fin.cons v a) + ∑ i, ∑ d, F v i d y) := by
          filter_upwards [hrec k hkN (Fin.cons v a)] with y hy
          simp only [Fin.cons_succ] at hy
          exact (eq_sub_iff_add_eq.mp hy).symm
        rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
        change ‖iteratedFDeriv ℝ j
          ((fun y => T (k + 1) y (Fin.cons v a)) + (fun y => ∑ i, ∑ d, F v i d y)) x‖ ≤ _
        rw [iteratedFDeriv_add_apply (i := j)
          (f := fun y => T (k + 1) y (Fin.cons v a))
          (g := fun y => ∑ i, ∑ d, F v i d y)
          ((hTs (k + 1) (by omega) (Fin.cons v a)).of_le (by exact_mod_cast le_top))
          ((ContDiffAt.sum fun i _ => ContDiffAt.sum fun d _ => hFs v i d).of_le
            (by exact_mod_cast le_top))]
        apply (norm_add_le _ _).trans
        calc
          _ ≤ L ^ j * A + (r + N : ℕ) * (Fintype.card ι : ℝ) *
              ((2 : ℝ) ^ N * D * (L ^ j * A)) :=
            add_le_add (ih j (by omega) (k + 1) (by omega) _) (hsum v)
          _ = _ := by ring
      apply (norm_iteratedFDeriv_succ_le_of_frame e ell hframe j
        ((hTs k (by omega) a).of_le (by exact_mod_cast le_top))).trans
      calc
        _ ≤ ∑ v, ‖ContinuousLinearMap.smulRightL ℝ E ℝ (ell v)‖ *
            ((1 + (r + N : ℕ) * (Fintype.card ι : ℝ) * (2 : ℝ) ^ N * D) *
              (L ^ j * A)) :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hdir v) (by positivity)
        _ = ((∑ v, ‖ContinuousLinearMap.smulRightL ℝ E ℝ (ell v)‖) *
            (1 + (r + N : ℕ) * (Fintype.card ι : ℝ) * (2 : ℝ) ^ N * D)) *
              (L ^ j * A) := by rw [← Finset.sum_mul]; ring
        _ ≤ L * (L ^ j * A) := mul_le_mul_of_nonneg_right hL (by positivity)
        _ = L ^ (j + 1) * A := by rw [pow_succ]; ring
