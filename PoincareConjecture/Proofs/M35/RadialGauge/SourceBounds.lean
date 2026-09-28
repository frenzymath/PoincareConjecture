import PoincareConjecture.Proofs.M35.RadialGauge.SourceSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}
variable {A : Type*} [Nonempty A]

local notation "V" => EuclideanSpace ℝ (Fin n)

omit [Nonempty A] in
private theorem bounded_derivatives_add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : A → V → F}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ∀ a, ContDiff ℝ ∞ (g a))
    (hfb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (f a) x‖ ≤ C)
    (hgb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (g a) x‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (fun y => f a y + g a y) x‖ ≤ C := by
  intro k
  obtain ⟨C, hC⟩ := hfb k
  obtain ⟨D, hD⟩ := hgb k
  refine ⟨C + D, fun a x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply
    ((hf a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt
    ((hg a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hC a x) (hD a x))

private theorem bounded_derivatives_clm_apply
    {W F : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : A → V → W →L[ℝ] F} {b : A → V → W}
    (hp : ∀ a, ContDiff ℝ ∞ (p a)) (hb : ∀ a, ContDiff ℝ ∞ (b a))
    (hpb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (p a) x‖ ≤ C)
    (hbb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (b a) x‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (fun y => p a y (b a y)) x‖ ≤ C := by
  classical
  choose P hP using hpb
  choose B hB using hbb
  have hP0 (j : ℕ) : 0 ≤ P j :=
    (norm_nonneg _).trans (hP j (Classical.choice ‹Nonempty A›) 0)
  intro k
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * P i * B (k - i), fun a x => ?_⟩
  apply (norm_iteratedFDeriv_clm_apply (hp a) (hb a) x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hP i a x) (Nat.cast_nonneg _)) (hB (k - i) a x)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hP0 i))

private theorem bounded_derivatives_mul {f g : A → V → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ∀ a, ContDiff ℝ ∞ (g a))
    (hfb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (f a) x‖ ≤ C)
    (hgb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (g a) x‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (fun y => f a y * g a y) x‖ ≤ C := by
  classical
  choose B hB using hfb
  choose C hC using hgb
  have hB0 (j : ℕ) : 0 ≤ B j :=
    (norm_nonneg _).trans (hB j (Classical.choice ‹Nonempty A›) 0)
  intro k
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * C (k - i), fun a x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (hf a) (hg a) x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hB i a x) (Nat.cast_nonneg _)) (hC (k - i) a x)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 i))

omit [Nonempty A] in
private theorem bounded_derivatives_sum {ι : Type*} [Fintype ι] {f : ι → A → V → ℝ}
    (hf : ∀ i a, ContDiff ℝ ∞ (f i a))
    (hfb : ∀ i k, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (f i a) x‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (fun y => ∑ i, f i a y) x‖ ≤ C := by
  classical
  choose C hC using hfb
  intro k
  refine ⟨∑ i, C i k, fun a x => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply
    (fun i _ => ((hf i a).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hC i k a x))

private theorem norm_iteratedFDeriv_id_le_one (j : ℕ) (hj : 1 ≤ j) (x : V) :
    ‖iteratedFDeriv ℝ j (fun y : V => y) x‖ ≤ 1 := by
  cases j with
  | zero => omega
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hid : fderiv ℝ (fun y : V => y) = fun _ => ContinuousLinearMap.id ℝ V := by
        funext y
        exact (hasFDerivAt_id y).fderiv
      rw [hid]
      cases j with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          exact ContinuousLinearMap.norm_id_le
      | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

omit [Nonempty A] in
private theorem bounded_forcing_composition
    {G : A → V → ℝ → ℝ} {u : A → V → ℝ} {eta : ℝ}
    (hG : ∀ a, ContDiff ℝ ∞ (fun p : V × ℝ => G a p.1 p.2))
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (huvalue : ∀ a x, |u a x| ≤ eta)
    (hub : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (u a) x‖ ≤ C)
    (hGb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ => G a p.1 p.2) (x, z)‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (fun y => G a y (u a y)) x‖ ≤ C := by
  classical
  choose U hU using hub
  choose B hB using hGb
  intro k
  let C := ∑ j ∈ Finset.range (k + 1), |B j|
  let D := 1 + ∑ j ∈ Finset.range (k + 1), |U j|
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (k + 1)) => abs_nonneg (U j))]
  have hBle {j : ℕ} (hj : j ≤ k) : B j ≤ C := by
    exact (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (B i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have hUle {j : ℕ} (hj : j ≤ k) : U j ≤ D := by
    have h := (le_abs_self (U j)).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (U i))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
    dsimp [D]
    linarith
  refine ⟨(k.factorial : ℝ) * C * D ^ k, fun a x => ?_⟩
  have h := norm_iteratedFDeriv_comp_le (hG a) (contDiff_id.prodMk (hu a))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) x
    (C := C) (D := D)
    (fun j hj => (hB j a x (u a x) (huvalue a x)).trans (hBle hj))
    (fun j hj hjk => ?_)
  · simpa only [Function.comp_def, id_eq] using h
  · rw [iteratedFDeriv_prodMk contDiffAt_id (hu a).contDiffAt
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j),
      ContinuousMultilinearMap.opNorm_prod]
    exact (max_le ((norm_iteratedFDeriv_id_le_one j hj x).trans hD)
      ((hU j a x).trans (hUle hjk))).trans (le_self_pow₀ hD (by omega))

theorem gaugeSource_uniform_bounded_derivatives
    {b : A → V → V} {G : A → V → ℝ → ℝ} {u : A → V → ℝ}
    {eta : ℝ} (hb : ∀ a, ContDiff ℝ ∞ (b a))
    (hG : ∀ a, ContDiff ℝ ∞ (fun p : V × ℝ => G a p.1 p.2))
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (huvalue : ∀ a x, |u a x| ≤ eta)
    (hbb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (b a) x‖ ≤ C)
    (hub : ∀ k : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ k (u a) x‖ ≤ C)
    (hGb : ∀ k : ℕ, ∃ C : ℝ, ∀ a x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ => G a p.1 p.2) (x, z)‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ a x,
      ‖iteratedFDeriv ℝ k (gaugeSource (b a) (G a) (u a)) x‖ ≤ C := by
  classical
  have hdu (a : A) := (contDiff_infty_iff_fderiv.mp (hu a)).2
  have hdub : ∀ k : ℕ, ∃ C : ℝ, ∀ a x,
      ‖iteratedFDeriv ℝ k (fderiv ℝ (u a)) x‖ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := hub (k + 1)
    exact ⟨C, fun a x => by simpa only [norm_iteratedFDeriv_fderiv] using hC a x⟩
  have hsquared : ∀ k : ℕ, ∃ C : ℝ, ∀ a x,
      ‖iteratedFDeriv ℝ k (fun y => ‖fderiv ℝ (u a) y‖ ^ 2) x‖ ≤ C := by
    simp_rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual]
    apply bounded_derivatives_sum
    · intro i a
      exact ((hdu a).clm_apply contDiff_const).pow 2
    · intro i
      have hi : ∀ k : ℕ, ∃ C : ℝ, ∀ a x,
          ‖iteratedFDeriv ℝ k (fun y => (fderiv ℝ (u a) y)
            ((EuclideanSpace.basisFun (Fin n) ℝ) i)) x‖ ≤ C := by
        intro k
        obtain ⟨C, hC⟩ := hdub k
        refine ⟨‖(EuclideanSpace.basisFun (Fin n) ℝ) i‖ * C, fun a x => ?_⟩
        exact (norm_iteratedFDeriv_clm_apply_const (hdu a).contDiffAt
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).trans
          (mul_le_mul_of_nonneg_left (hC a x) (norm_nonneg _))
      simpa only [pow_two] using bounded_derivatives_mul
        (fun a => (hdu a).clm_apply contDiff_const)
        (fun a => (hdu a).clm_apply contDiff_const) hi hi
  exact bounded_derivatives_add
    (fun a => ((hdu a).clm_apply (hb a)).add (contDiff_squared_dual_norm (hdu a)))
    (fun a => (hG a).comp (contDiff_id.prodMk (hu a)))
    (bounded_derivatives_add (fun a => (hdu a).clm_apply (hb a))
      (fun a => contDiff_squared_dual_norm (hdu a))
      (bounded_derivatives_clm_apply hdu hb hdub hbb) hsquared)
    (bounded_forcing_composition hG hu huvalue hub hGb)

end PoincareConjecture.M35.RadialGauge
