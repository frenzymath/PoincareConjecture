import PoincareConjecture.Proofs.M34.Mathlib.FiniteJetNormBounds
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound

set_option autoImplicit false

open Filter
open scoped ContDiff BigOperators Topology
open Poincare.Analysis.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι]

theorem norm_covariantArray_jet_le_of_total_order
    (e : ι → E) (r N : ℕ) (x : E)
    (Γ : E → ι → ι → ι → ℝ)
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
    (hL : (∑ i : ι, ‖ContinuousLinearMap.apply ℝ ℝ (e i)‖) +
      (r + N : ℕ) * (Fintype.card ι : ℝ) * (2 : ℝ) ^ N * D ≤ L)
    (hΓ : ∀ j ≤ N, ∀ a b d, ‖iteratedFDeriv ℝ j
      (fun y => Γ y a b d) x‖ ≤ D)
    (hb : ∀ j ≤ N, ∀ a, ‖iteratedFDeriv ℝ j (fun y => T 0 y a) x‖ ≤ A)
    (k j : ℕ) (hkj : k + j ≤ N) (a : Fin (r + k) → ι) :
    ‖iteratedFDeriv ℝ j (fun y => T k y a) x‖ ≤ L ^ k * A := by
  classical
  have hL₀ : 0 ≤ L := zero_le_one.trans hL₁
  induction k generalizing j with
  | zero => simpa only [pow_zero, one_mul] using hb j (by simpa using hkj) a
  | succ k ih =>
    let V : ℝ := ∑ i : ι, ‖ContinuousLinearMap.apply ℝ ℝ (e i)‖
    have hV : 0 ≤ V := Finset.sum_nonneg fun i _ =>
      norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (e i))
    have hsmooth (b : Fin (r + k) → ι) :
        ContDiffAt ℝ ∞ (fun y => T k y b) x := hTs k (by omega) b
    have hbound (l : ℕ) (hl : k + l ≤ N) (b : Fin (r + k) → ι) :
        ‖iteratedFDeriv ℝ l (fun y => T k y b) x‖ ≤ L ^ k * A := ih l hl b
    let F := fun (i : Fin (r + k)) (d : ι) y =>
      Γ y d (a ⟨0, by omega⟩) (a i.succ) *
        T k y (Function.update (fun l => a l.succ) i d)
    have hFs (i : Fin (r + k)) (d : ι) : ContDiffAt ℝ ∞ (F i d) x :=
      (hΓs _ _ _).mul (hsmooth _)
    have hFb (i : Fin (r + k)) (d : ι) :
        ‖iteratedFDeriv ℝ j (F i d) x‖ ≤ (2 : ℝ) ^ N * D * (L ^ k * A) := by
      have hmul := norm_iteratedFDeriv_bilinear_le_of_jet_bounds
        (ContinuousLinearMap.mul ℝ ℝ) (hΓs d (a ⟨0, by omega⟩) (a i.succ))
        (hsmooth (Function.update (fun l => a l.succ) i d)) j hD
        (fun l hl => hΓ l (by omega) d (a ⟨0, by omega⟩) (a i.succ))
        (fun l hl => hbound l (by omega) _)
      simp only [ContinuousLinearMap.opNorm_mul, one_mul] at hmul
      exact hmul.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : j ≤ N)) hD)
        (mul_nonneg (pow_nonneg hL₀ _) hA))
    have hsum : ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ d, F i d y) x‖ ≤
        (r + N : ℕ) * (Fintype.card ι : ℝ) *
          ((2 : ℝ) ^ N * D * (L ^ k * A)) := by
      calc
        _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => ∑ d, F i d y) x‖ :=
          norm_iteratedFDeriv_sum_le_of_contDiffAt Finset.univ j
            (fun i _ => (ContDiffAt.sum fun d _ => hFs i d).of_le
              (by exact_mod_cast le_top))
        _ ≤ ∑ i, ∑ d, ‖iteratedFDeriv ℝ j (F i d) x‖ :=
          Finset.sum_le_sum fun i _ => norm_iteratedFDeriv_sum_le_of_contDiffAt
            Finset.univ j (fun d _ => (hFs i d).of_le (by exact_mod_cast le_top))
        _ ≤ ∑ _i : Fin (r + k), ∑ _d : ι, (2 : ℝ) ^ N * D * (L ^ k * A) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun d _ => hFb i d
        _ = (r + k : ℕ) * (Fintype.card ι : ℝ) *
            ((2 : ℝ) ^ N * D * (L ^ k * A)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast (by omega : r + k ≤ r + N)
    have hd : ‖iteratedFDeriv ℝ j (fun y =>
        fderiv ℝ (fun z => T k z (fun i => a i.succ)) y (e (a ⟨0, by omega⟩))) x‖ ≤
        V * (L ^ k * A) := by
      apply (norm_iteratedFDeriv_directional_le j
        ((hsmooth _).of_le (by exact_mod_cast le_top)) _).trans
      apply mul_le_mul
      · exact Finset.single_le_sum (fun i _ =>
          norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (e i)))
          (Finset.mem_univ (a ⟨0, by omega⟩))
      · exact hbound (j + 1) (by omega) _
      · exact norm_nonneg _
      · exact hV
    have hds := ((hsmooth (fun i => a i.succ)).fderiv_right
      (m := ∞) (by simp)).clm_apply (contDiffAt_const (c := e (a ⟨0, by omega⟩)))
    have hsub := norm_iteratedFDeriv_sub_le_of_contDiffAt j
      (f := fun y => fderiv ℝ (fun z => T k z (fun i => a i.succ)) y
        (e (a ⟨0, by omega⟩)))
      (g := fun y => ∑ i, ∑ d, F i d y)
      (hds.of_le (by exact_mod_cast le_top))
      ((ContDiffAt.sum fun i _ => ContDiffAt.sum fun d _ => hFs i d).of_le
        (by exact_mod_cast le_top))
    rw [((hrec k (by omega) a).iteratedFDeriv ℝ j).self_of_nhds]
    apply hsub.trans
    calc
      _ ≤ V * (L ^ k * A) + (r + N : ℕ) * (Fintype.card ι : ℝ) *
          ((2 : ℝ) ^ N * D * (L ^ k * A)) := add_le_add hd hsum
      _ = (V + (r + N : ℕ) * (Fintype.card ι : ℝ) * (2 : ℝ) ^ N * D) *
          (L ^ k * A) := by ring
      _ ≤ L * (L ^ k * A) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = L ^ (k + 1) * A := by rw [pow_succ]; ring
