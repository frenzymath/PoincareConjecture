import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.Model
import PoincareConjecture.Proofs.M32.Claim11_35.NeckCovariantJets



















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.M32

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates




theorem evolving_covariant_component_center_le {epsilon tau : ℝ}
    (hepsilon : 0 < epsilon) (htau : tau ∈ Icc (-1) 0)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon tau B)
    (q : UnitTwoSphere) {z : ℝ} (hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊) (a : Fin (2 + k) → Fin 3) :
    |roundCylinderIteratedDerivative tau (chartAt E2 q) B k (0, z) a| ≤
      (2 : ℝ) ^ (2 + k) * epsilon := by
  classical
  have htau1 : tau < 1 := lt_of_le_of_lt htau.2 zero_lt_one
  let w : Fin 3 → ℝ := ![(2 * (1 - tau))⁻¹, (2 * (1 - tau))⁻¹, 1]
  have hweight (i : Fin 3) : (1 / 4 : ℝ) ≤ w i := by
    have hpos : 0 < 2 * (1 - tau) := by linarith [htau.2]
    have hle : (2 * (1 - tau)) ≤ 4 := by linarith [htau.1]
    have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) hpos).mpr hle
    fin_cases i
    · simpa [w] using h
    · simpa [w] using h
    · norm_num [w]
  have hweight0 (i : Fin 3) : 0 ≤ w i := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans (hweight i)
  have hnorm0 {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
      0 ≤ roundCylinderTensorNormSquared tau (chartAt E2 q) (0, z) T := by
    rw [evolving_roundCylinderTensorNormSquared_center htau1]
    exact Finset.sum_nonneg fun b _ => mul_nonneg
      (Finset.prod_nonneg fun i _ => hweight0 (b i)) (sq_nonneg _)
  let T := roundCylinderIteratedDerivative tau (chartAt E2 q) B k (0, z)
  have hcomponent : (1 / 4 : ℝ) ^ (2 + k) * (T a) ^ 2 ≤
      roundCylinderTensorNormSquared tau (chartAt E2 q) (0, z) T := by
    have hprod : (1 / 4 : ℝ) ^ (2 + k) ≤ ∏ i, w (a i) := by
      calc
        _ = ∏ _i : Fin (2 + k), (1 / 4 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (by intros; norm_num) (fun i _ => hweight (a i))
    rw [evolving_roundCylinderTensorNormSquared_center htau1]
    exact (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)).trans
      (Finset.single_le_sum (fun b _ => mul_nonneg
        (Finset.prod_nonneg fun i _ => hweight0 (b i)) (sq_nonneg _)) (Finset.mem_univ a))
  have hterm : roundCylinderTensorNormSquared tau (chartAt E2 q) (0, z) T ≤
      roundCylinderJetErrorSquared tau B ⌊epsilon⁻¹⌋₊ (q, z) := by
    unfold roundCylinderJetErrorSquared
    dsimp only
    rw [sphere_chart_center]
    exact Finset.single_le_sum (f := fun l =>
      roundCylinderTensorNormSquared tau (chartAt E2 q) (0, z)
        (roundCylinderIteratedDerivative tau (chartAt E2 q) B l (0, z)))
      (fun l _ => hnorm0 _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  obtain ⟨bound, hbound, hjet⟩ := hB.2
  have hweighted := hcomponent.trans (hterm.trans ((hjet (q, z) hz).trans hbound.le))
  have hcancel : (1 / 4 : ℝ) ^ (2 + k) * ((2 : ℝ) ^ (2 + k)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow]
    norm_num
  have hsquared := mul_le_mul_of_nonneg_left hweighted (sq_nonneg ((2 : ℝ) ^ (2 + k)))
  rw [← mul_assoc, mul_comm (((2 : ℝ) ^ (2 + k)) ^ 2), hcancel, one_mul] at hsquared
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) hepsilon.le)).mp
  rw [sq_abs, mul_pow]
  exact hsquared




theorem evolving_covariant_contDiffAt {epsilon tau : ℝ} (htau : tau < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon tau B)
    (q : UnitTwoSphere) {p : V} (hp : p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderIteratedDerivative tau
      (chartAt E2 q) B k y a) p := by
  induction k with
  | zero =>
      apply ((hB.1 q (a 0) (a 1)).contDiffAt ?_).sub
        (contDiff_roundCylinderGram tau q (a 0) (a 1)).contDiffAt
      rw [roundCylinder_sphereChart_target]
      exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp⟩
  | succ k ih =>
      exact (((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply
        contDiffAt_const).sub (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
          (contDiff_roundCylinderChristoffel htau q j (a 0) (a i.succ)).contDiffAt.mul
            (ih (Function.update (fun l => a l.succ) i j)))

private theorem evolving_norm_iteratedFDeriv_succ_le_of_basis_bound
    {f : V → ℝ} {x : V} (hf : ContDiffAt ℝ ∞ f x) (r : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i : Fin 3, ‖iteratedFDeriv ℝ r
      (fun p => fderiv ℝ f p (roundCylinderCoordinateBasis i)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ (r + 1) f x‖ ≤ 3 * C := by
  rw [← norm_iteratedFDeriv_fderiv]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (by simp)
  have h := norm_le_of_cylinder_basis_bound (iteratedFDeriv ℝ r (fderiv ℝ f) x v)
    (mul_nonneg hC hp) (fun i => ?_)
  · exact h.trans_eq (by ring)
  · have heq := congrArg (fun T => T v)
      ((ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)).iteratedFDeriv_comp_left
        (hf.fderiv_right (m := ∞) (by simp)) (by exact_mod_cast le_top))
    change iteratedFDeriv ℝ r
      (fun p => fderiv ℝ f p (roundCylinderCoordinateBasis i)) x v =
        iteratedFDeriv ℝ r (fderiv ℝ f) x v (roundCylinderCoordinateBasis i) at heq
    rw [← heq]
    exact (ContinuousMultilinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (hb i) hp)





theorem exists_evolving_covariant_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {epsilon tau : ℝ}, 0 < epsilon → epsilon ≤ 1 / 4 →
      tau ∈ Icc (-1) 0 → ∀ {A : RoundCylinderTwoTensor},
      RoundCylinderClose epsilon tau A → ∀ (q : UnitTwoSphere) {z : ℝ},
      z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ j k : ℕ, j + k ≤ 4 →
      ∀ a : Fin (2 + k) → Fin 3,
        ‖iteratedFDeriv ℝ j (fun p => roundCylinderIteratedDerivative tau
          (chartAt E2 q) A k p a) (0, z)‖ ≤ C * epsilon := by
  classical
  obtain ⟨J, hJ, hJbound⟩ := exists_roundCylinderChristoffel_threeJet_center_bound
  let L : ℝ := 3 * (1 + 144 * J)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  let B : ℕ → ℝ := fun r => 64 * L ^ r
  have hBpos (r : ℕ) : 0 < B r :=
    mul_pos (by norm_num) (pow_pos (lt_of_lt_of_le zero_lt_one hL) _)
  have hBmono : Monotone B := fun r s hrs =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hrs) (by norm_num)
  refine ⟨B 4, hBpos 4, ?_⟩
  intro epsilon tau hepsilon hsmall htau A hA q z hz j k hjk a
  have htau1 : tau < 1 := lt_of_le_of_lt htau.2 zero_lt_one
  have hfour : 4 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply (Nat.le_floor_iff (inv_nonneg.mpr hepsilon.le)).mpr
    rw [← one_div, le_div_iff₀ hepsilon]
    norm_num
    linarith
  let T (k : ℕ) (a : Fin (2 + k) → Fin 3) (p : V) :=
    roundCylinderIteratedDerivative tau (chartAt E2 q) A k p a
  have hT (k : ℕ) (a : Fin (2 + k) → Fin 3) : ContDiffAt ℝ ∞ (T k a) (0, z) :=
    evolving_covariant_contDiffAt htau1 hA q hz k a
  have hbound : ∀ r : ℕ, r ≤ 4 → ∀ j : ℕ, j ≤ r → ∀ k : ℕ, j + k ≤ 4 →
      ∀ a : Fin (2 + k) → Fin 3,
        ‖iteratedFDeriv ℝ j (T k a) (0, z)‖ ≤ B r * epsilon := by
    intro r
    induction r with
    | zero =>
        intro _ j hj k hk a
        have hj0 : j = 0 := by omega
        subst j
        rw [norm_iteratedFDeriv_zero]
        have h := evolving_covariant_component_center_le hepsilon htau hA q hz
          (k := k) (by omega) a
        have hpow : (2 : ℝ) ^ (2 + k) ≤ 64 := by
          have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num)
            (show 2 + k ≤ 6 by omega)
          norm_num at h ⊢
          exact h
        exact h.trans ((mul_le_mul_of_nonneg_right hpow hepsilon.le).trans_eq (by simp [B]))
    | succ r ih =>
        intro hr j hj k hk a
        by_cases hjold : j ≤ r
        · exact (ih (by omega) j hjold k hk a).trans
            (mul_le_mul_of_nonneg_right (hBmono (Nat.le_succ r)) hepsilon.le)
        have hjeq : j = r + 1 := by omega
        subst j
        have hr3 : r ≤ 3 := by omega
        have hk4 : (k : ℝ) ≤ 4 := by exact_mod_cast (show k ≤ 4 by omega)
        have hlow (m : ℕ) (hm : m ≤ r) (b : Fin (2 + k) → Fin 3) :
            ‖iteratedFDeriv ℝ m (T k b) (0, z)‖ ≤ B r * epsilon :=
          ih (by omega) m hm k (by omega) b
        have hproduct (i b c : Fin 3) (a : Fin (2 + k) → Fin 3) :
            ‖iteratedFDeriv ℝ r (fun p => roundCylinderChristoffel 0
              (chartAt E2 q) p b i c * T k a p) (0, z)‖ ≤
              8 * J * B r * epsilon := by
          have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
            (contDiff_roundCylinderChristoffel (u := 0) (by norm_num) q b i c).contDiffAt
            (hT k a) r
          simp only [smul_eq_mul] at h
          apply h.trans
          have hchoose : (∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ)) = (2 : ℝ) ^ r := by
            exact_mod_cast Nat.sum_range_choose r
          have hpow : (2 : ℝ) ^ r ≤ 8 := by
            have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hr3
            norm_num at h
            exact h
          calc
            _ ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * J *
                (B r * epsilon) := by
              apply Finset.sum_le_sum
              intro l hl
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left
                  (hJbound q z l (by have := Finset.mem_range.mp hl; omega) b i c)
                  (Nat.cast_nonneg _))
                (hlow (r - l) (Nat.sub_le _ _) a) (norm_nonneg _)
                (mul_nonneg (Nat.cast_nonneg _) hJ.le)
            _ = (2 : ℝ) ^ r * J * (B r * epsilon) := by
              rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
            _ ≤ 8 * J * (B r * epsilon) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hJ.le)
                (mul_nonneg (hBpos r).le hepsilon.le)
            _ = _ := by ring
        have hdirection (i : Fin 3) :
            ‖iteratedFDeriv ℝ r (fun p => fderiv ℝ (T k a) p
              (roundCylinderCoordinateBasis i)) (0, z)‖ ≤
              (1 + 144 * J) * B r * epsilon := by
          let H (l : Fin (2 + k)) (b : Fin 3) (p : V) :=
            roundCylinderChristoffel 0 (chartAt E2 q) p b i (a l) *
              T k (Function.update a l b) p
          have hH (l : Fin (2 + k)) (b : Fin 3) : ContDiffAt ℝ ∞ (H l b) (0, z) :=
            (contDiff_roundCylinderChristoffel (u := 0) (by norm_num) q b i (a l)).contDiffAt.mul
              (hT k _)
          have hsumSmooth : ContDiffAt ℝ ∞ (fun p => ∑ l, ∑ b, H l b p) (0, z) :=
            ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun b _ => hH l b))
          have hinner (l : Fin (2 + k)) :
              ‖iteratedFDeriv ℝ r (fun p => ∑ b, H l b p) (0, z)‖ ≤
                3 * (8 * J * B r * epsilon) := by
            simpa only [Fintype.card_fin, Nat.cast_ofNat] using
              CoordinateExponential.norm_iteratedFDeriv_sum_le_const
                (fun b => (hH l b).of_le (by exact_mod_cast le_top))
                (fun b => hproduct i b (a l) (Function.update a l b))
          have hsum : ‖iteratedFDeriv ℝ r (fun p => ∑ l, ∑ b, H l b p) (0, z)‖ ≤
              144 * J * B r * epsilon := by
            calc
              _ ≤ (2 + k : ℕ) * (3 * (8 * J * B r * epsilon)) := by
                simpa only [Fintype.card_fin] using
                  CoordinateExponential.norm_iteratedFDeriv_sum_le_const
                    (fun l => (ContDiffAt.sum (fun b _ => hH l b)).of_le
                      (by exact_mod_cast le_top)) hinner
              _ = (3 * (2 + (k : ℝ))) * (8 * J * B r * epsilon) := by
                push_cast
                ring
              _ ≤ 18 * (8 * J * B r * epsilon) :=
                mul_le_mul_of_nonneg_right (by linarith)
                  (by have := hBpos r; positivity)
              _ = _ := by ring
          have heq : (fun p => fderiv ℝ (T k a) p (roundCylinderCoordinateBasis i)) =
              fun p => T (k + 1) (Fin.cons i a) p + ∑ l, ∑ b, H l b p := by
            funext p
            dsimp only [T, H]
            simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
              Fin.cons_zero, Fin.cons_succ, evolving_roundCylinderChristoffel_eq_zero htau1]
            exact (sub_add_cancel _ _).symm
          rw [heq, fun_iteratedFDeriv_add_apply
            ((hT (k + 1) _).of_le (by exact_mod_cast le_top))
            (hsumSmooth.of_le (by exact_mod_cast le_top))]
          exact (norm_add_le _ _).trans
            ((add_le_add (ih (by omega) r le_rfl (k + 1) (by omega) _) hsum).trans_eq (by ring))
        have hnext := evolving_norm_iteratedFDeriv_succ_le_of_basis_bound (hT k a) r
          (C := (1 + 144 * J) * B r * epsilon) (by have := hBpos r; positivity) hdirection
        exact hnext.trans_eq (by dsimp [B, L]; rw [pow_succ]; ring)
  exact hbound 4 le_rfl j (by omega) k hjk a

end PoincareConjecture.M32
