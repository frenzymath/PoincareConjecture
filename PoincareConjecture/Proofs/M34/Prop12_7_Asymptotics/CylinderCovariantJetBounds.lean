import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderConnectionParameterBounds
import PoincareConjecture.Proofs.M34.Mathlib.FiniteJetNormBounds
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff BigOperators
open Poincare.Analysis.Calculus

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem roundCylinderIteratedDerivative_contDiffAt {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) {B : RoundCylinderTwoTensor} {x : RoundCylinderCoordinates}
    (hB : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderGram u (chartAt E₂ q) y a b) x)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y =>
      roundCylinderIteratedDerivative u (chartAt E₂ q) B k y a) x := by
  induction k with
  | zero => exact hB (a 0) (a 1)
  | succ k ih =>
    exact (((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply
        contDiffAt_const).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (contDiff_roundCylinderChristoffel hu q j (a 0) (a i.succ)).contDiffAt.mul
          (ih (Function.update (fun l => a l.succ) i j)))

private theorem norm_covariant_jet_le_of_total_order
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (B : RoundCylinderTwoTensor)
    (x : RoundCylinderCoordinates) (N : ℕ) {D L A : ℝ}
    (hD : 0 ≤ D) (hL₁ : 1 ≤ L) (hA : 0 ≤ A)
    (hL : (∑ i : Fin 3,
        ‖ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)‖) +
      (2 + N : ℕ) * 3 * (2 : ℝ) ^ N * D ≤ L)
    (hΓ : ∀ j ≤ N, ∀ a b d : Fin 3, ‖iteratedFDeriv ℝ j
      (fun y => roundCylinderChristoffel u (chartAt E₂ q) y a b d) x‖ ≤ D)
    (hs : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderGram u (chartAt E₂ q) y a b) x)
    (hb : ∀ j ≤ N, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
        roundCylinderGram u (chartAt E₂ q) y a b) x‖ ≤ A)
    (k j : ℕ) (hkj : k + j ≤ N) (a : Fin (2 + k) → Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderIteratedDerivative u (chartAt E₂ q) B k y a) x‖ ≤ L ^ k * A := by
  classical
  have hL₀ : 0 ≤ L := zero_le_one.trans hL₁
  induction k generalizing j with
  | zero =>
    simpa only [roundCylinderIteratedDerivative, pow_zero, one_mul] using
      hb j (by simpa using hkj) (a 0) (a 1)
  | succ k ih =>
    let V : ℝ := ∑ i : Fin 3,
      ‖ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)‖
    have hV : 0 ≤ V := Finset.sum_nonneg fun i _ =>
      norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i))
    let T := fun (b : Fin (2 + k) → Fin 3) y =>
      roundCylinderIteratedDerivative u (chartAt E₂ q) B k y b
    have hTs (b : Fin (2 + k) → Fin 3) : ContDiffAt ℝ ∞ (T b) x :=
      roundCylinderIteratedDerivative_contDiffAt hu q hs k b
    have hTb (l : ℕ) (hl : k + l ≤ N) (b : Fin (2 + k) → Fin 3) :
        ‖iteratedFDeriv ℝ l (T b) x‖ ≤ L ^ k * A := ih l hl b
    let F := fun (i : Fin (2 + k)) (d : Fin 3) y =>
      roundCylinderChristoffel u (chartAt E₂ q) y d (a 0) (a i.succ) *
        T (Function.update (fun l => a l.succ) i d) y
    have hFs (i : Fin (2 + k)) (d : Fin 3) : ContDiffAt ℝ ∞ (F i d) x :=
      (contDiff_roundCylinderChristoffel hu q d (a 0) (a i.succ)).contDiffAt.mul (hTs _)
    have hFb (i : Fin (2 + k)) (d : Fin 3) :
        ‖iteratedFDeriv ℝ j (F i d) x‖ ≤ (2 : ℝ) ^ N * D * (L ^ k * A) := by
      have hmul := norm_iteratedFDeriv_bilinear_le_of_jet_bounds
        (ContinuousLinearMap.mul ℝ ℝ)
        (contDiff_roundCylinderChristoffel hu q d (a 0) (a i.succ)).contDiffAt
        (hTs (Function.update (fun l => a l.succ) i d)) j hD
        (fun l hl => hΓ l (by omega) _ _ _) (fun l hl => hTb l (by omega) _)
      simp only [ContinuousLinearMap.opNorm_mul, one_mul] at hmul
      exact hmul.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (by omega : j ≤ N)) hD)
        (mul_nonneg (pow_nonneg hL₀ _) hA))
    have hsum : ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ d, F i d y) x‖ ≤
        (2 + N : ℕ) * 3 * ((2 : ℝ) ^ N * D * (L ^ k * A)) := by
      calc
        _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => ∑ d, F i d y) x‖ :=
          norm_iteratedFDeriv_sum_le_of_contDiffAt Finset.univ j
            (fun i _ => (ContDiffAt.sum fun d _ => hFs i d).of_le
              (by exact_mod_cast le_top))
        _ ≤ ∑ i, ∑ d, ‖iteratedFDeriv ℝ j (F i d) x‖ :=
          Finset.sum_le_sum fun i _ => norm_iteratedFDeriv_sum_le_of_contDiffAt
            Finset.univ j (fun d _ => (hFs i d).of_le (by exact_mod_cast le_top))
        _ ≤ ∑ _i : Fin (2 + k), ∑ _d : Fin 3, (2 : ℝ) ^ N * D * (L ^ k * A) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun d _ => hFb i d
        _ = (2 + k : ℕ) * 3 * ((2 : ℝ) ^ N * D * (L ^ k * A)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact_mod_cast (by omega : 2 + k ≤ 2 + N)
    have hd : ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (T (fun i => a i.succ)) y
        (roundCylinderCoordinateBasis (a 0))) x‖ ≤ V * (L ^ k * A) := by
      apply (norm_iteratedFDeriv_directional_le j
        ((hTs _).of_le (by exact_mod_cast le_top)) _).trans
      apply mul_le_mul
      · exact Finset.single_le_sum (fun i _ =>
          norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)))
          (Finset.mem_univ (a 0))
      · exact hTb (j + 1) (by omega) _
      · exact norm_nonneg _
      · exact hV
    have hds := ((hTs (fun i => a i.succ)).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := roundCylinderCoordinateBasis (a 0)))
    have hsub := norm_iteratedFDeriv_sub_le_of_contDiffAt j
      (f := fun y => fderiv ℝ (T (fun i => a i.succ)) y (roundCylinderCoordinateBasis (a 0)))
      (g := fun y => ∑ i, ∑ d, F i d y)
      (hds.of_le (by exact_mod_cast le_top))
      ((ContDiffAt.sum fun i _ => ContDiffAt.sum fun d _ => hFs i d).of_le
        (by exact_mod_cast le_top))
    apply hsub.trans
    calc
      _ ≤ V * (L ^ k * A) +
          (2 + N : ℕ) * 3 * ((2 : ℝ) ^ N * D * (L ^ k * A)) := add_le_add hd hsum
      _ = (V + (2 + N : ℕ) * 3 * (2 : ℝ) ^ N * D) * (L ^ k * A) := by ring
      _ ≤ L * (L ^ k * A) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = L ^ (k + 1) * A := by rw [pow_succ]; ring

theorem exists_roundCylinder_covariant_component_bound
    {T : ℝ} (hT : T < 1) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (0 : ℝ) T,
      ∀ (q : UnitTwoSphere) (B : RoundCylinderTwoTensor) (x : RoundCylinderCoordinates),
      x ∈ K → ∀ A : ℝ, 0 ≤ A →
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderGram u (chartAt E₂ q) y a b) x) →
      (∀ j ≤ N, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderGram u (chartAt E₂ q) y a b) x‖ ≤ A) →
      ∀ k ≤ N, ∀ a : Fin (2 + k) → Fin 3,
        |roundCylinderIteratedDerivative u (chartAt E₂ q) B k x a| ≤ C * A := by
  classical
  choose D hD hDb using fun j : Fin (N + 1) =>
    roundCylinderChristoffel_uniform_spatial_jet_bound hT hK j
  let D₀ : ℝ := ∑ j : Fin (N + 1), D j
  have hD₀ : 0 ≤ D₀ := Finset.sum_nonneg fun j _ => hD j
  let L : ℝ := max 1 ((∑ i : Fin 3,
    ‖ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)‖) +
      (2 + N : ℕ) * 3 * (2 : ℝ) ^ N * D₀)
  have hL₁ : 1 ≤ L := le_max_left _ _
  refine ⟨L ^ N, pow_nonneg (zero_le_one.trans hL₁) _, ?_⟩
  intro u hu q B x hx A hA hs hb k hk a
  have hΓ (j : ℕ) (hj : j ≤ N) (a b d : Fin 3) :
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderChristoffel u (chartAt E₂ q) y a b d) x‖ ≤ D₀ := by
    let l : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hDb l u hu q x hx a b d).trans
      (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ l))
  have h := norm_covariant_jet_le_of_total_order (hu.2.trans_lt hT) q B x N
    hD₀ hL₁ hA (le_max_right _ _) hΓ hs hb k 0 (by simpa using hk) a
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL₁ hk) hA)

end PoincareConjecture.M34
