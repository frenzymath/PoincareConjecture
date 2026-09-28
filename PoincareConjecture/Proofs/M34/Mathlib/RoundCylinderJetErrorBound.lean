import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import PoincareConjecture.Proofs.M34.Mathlib.SphereChartMetric
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem sphere_chart_center_zero (q : UnitTwoSphere) :
    chartAt E₂ q q = 0 := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  change stereographic' 2 (-q) q = 0
  change (OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere (-q))).repr
      (stereographic (norm_eq_of_mem_sphere (-q)) q) = 0
  rw [stereographic_neg_apply, map_zero]

theorem roundCylinderGram_chart_center (u : ℝ) (q : UnitTwoSphere) (r : ℝ) :
    roundCylinderGram u (chartAt E₂ q) (chartAt E₂ q q, r) =
      Matrix.diagonal ![2 * (1 - u), 2 * (1 - u), 1] := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  rw [sphere_chart_center_zero]
  ext i j
  change 2 * (1 - u) * inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => (z : E₃))
        ((chartAt E₂ q).symm 0)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm 0
          (roundCylinderCoordinateBasis i).1))
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => (z : E₃))
        ((chartAt E₂ q).symm 0)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm 0
          (roundCylinderCoordinateBasis j).1)) +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 = _
  have hpair := inner_mfderiv_sphere_chart_symm (E := E₃) (n := 2) q (0 : E₂)
    (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1
  have hrho : (16 : ℝ) / (‖(0 : E₂)‖ ^ 2 + 4) ^ 2 = 1 := by norm_num
  rw [hpair, hrho, one_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]

theorem roundCylinderGram_chart_center_inv {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (r : ℝ) :
    (roundCylinderGram u (chartAt E₂ q) (chartAt E₂ q q, r))⁻¹ =
      Matrix.diagonal ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] := by
  have hne : (2 * (1 - u) : ℝ) ≠ 0 := by
    have : (1 - u : ℝ) ≠ 0 := sub_ne_zero.mpr hu.symm
    exact mul_ne_zero two_ne_zero this
  apply Matrix.inv_eq_right_inv
  rw [roundCylinderGram_chart_center, Matrix.diagonal_mul_diagonal]
  have hvec :
      (![2 * (1 - u), 2 * (1 - u), 1] *
        ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] : Fin 3 → ℝ) = 1 := by
    ext i
    fin_cases i
    · exact mul_inv_cancel₀ hne
    · exact mul_inv_cancel₀ hne
    · exact one_mul (1 : ℝ)
  change Matrix.diagonal
      (![2 * (1 - u), 2 * (1 - u), 1] *
        ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1]) = 1
  rw [hvec]
  exact Matrix.diagonal_one

theorem roundCylinderGram_chart_center_inv_le {T : ℝ} (hT : T < 1)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (q : UnitTwoSphere) (r : ℝ)
    (i j : Fin 3) :
    |((roundCylinderGram u (chartAt E₂ q) (chartAt E₂ q q, r))⁻¹ i j)| ≤
      max 1 ((2 * (1 - T))⁻¹) := by
  have hu1 : u ≠ 1 := (hu.2.trans_lt hT).ne
  have hpos : 0 < 1 - T := sub_pos.mpr hT
  have hle : 0 < 1 - u := sub_pos.mpr (hu.2.trans_lt hT)
  have hinv :
      (2 * (1 - u))⁻¹ ≤ (2 * (1 - T))⁻¹ :=
    inv_anti₀ (mul_pos two_pos hpos)
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hu.2 1) two_pos.le)
  rw [roundCylinderGram_chart_center_inv hu1 q r, Matrix.diagonal_apply]
  split_ifs with hij
  · subst j
    fin_cases i
    · change |(2 * (1 - u))⁻¹| ≤ _
      rw [abs_of_pos (inv_pos.mpr (mul_pos two_pos hle))]
      exact hinv.trans (le_max_right _ _)
    · change |(2 * (1 - u))⁻¹| ≤ _
      rw [abs_of_pos (inv_pos.mpr (mul_pos two_pos hle))]
      exact hinv.trans (le_max_right _ _)
    · change |(1 : ℝ)| ≤ _
      rw [abs_one]
      exact le_max_left _ _
  · rw [abs_zero]
    exact zero_le_one.trans (le_max_left _ _)

theorem roundCylinderTensorNormSquared_le {u : ℝ}
    (c : OpenPartialHomeomorph UnitTwoSphere E₂)
    (p : RoundCylinderCoordinates) {r : ℕ}
    (T : (Fin r → Fin 3) → ℝ) {M δ : ℝ} (hM : 0 ≤ M)
    (hinv : ∀ i j, |((roundCylinderGram u c p)⁻¹ i j)| ≤ M)
    (hT : ∀ a, |T a| ≤ δ) :
    roundCylinderTensorNormSquared u c p T ≤
      ((3 : ℝ) ^ r) ^ 2 * M ^ r * δ ^ 2 := by
  classical
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hT fun _ => 0)
  have hab (a b : Fin r → Fin 3) :
      |∏ i, (roundCylinderGram u c p)⁻¹ (a i) (b i)| ≤ M ^ r := by
    rw [Finset.abs_prod]
    calc
      (∏ i, |(roundCylinderGram u c p)⁻¹ (a i) (b i)|) ≤ ∏ _i : Fin r, M :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hinv _ _
      _ = M ^ r := by simp [Finset.prod_const, Finset.card_univ]
  have hterm (a b : Fin r → Fin 3) :
      |((∏ i, (roundCylinderGram u c p)⁻¹ (a i) (b i)) * T a * T b)| ≤
        M ^ r * δ ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ M ^ r * δ * δ := by
        refine mul_le_mul ?_ (hT b) (abs_nonneg _) (mul_nonneg (pow_nonneg hM _) hδ)
        exact mul_le_mul (hab a b) (hT a) (abs_nonneg _) (pow_nonneg hM _)
      _ = M ^ r * δ ^ 2 := by ring
  apply (le_abs_self _).trans
  unfold roundCylinderTensorNormSquared
  rw [← Real.norm_eq_abs]
  refine (norm_sum_le _ _).trans ?_
  have hinner (a : Fin r → Fin 3) :
      ‖∑ b, (∏ i, (roundCylinderGram u c p)⁻¹ (a i) (b i)) * T a * T b‖ ≤
        (3 : ℝ) ^ r * M ^ r * δ ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc
      ∑ b, ‖(∏ i, (roundCylinderGram u c p)⁻¹ (a i) (b i)) * T a * T b‖ ≤
          ∑ _b : Fin r → Fin 3, M ^ r * δ ^ 2 :=
        Finset.sum_le_sum fun b _ => by
          rw [Real.norm_eq_abs]
          exact hterm a b
      _ = (3 : ℝ) ^ r * M ^ r * δ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
  refine (Finset.sum_le_sum fun a _ => hinner a).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact le_of_eq (by ring)

theorem roundCylinderJetErrorSquared_le {u : ℝ} {B : RoundCylinderTwoTensor}
    {order : ℕ} {z : RoundCylinderSpace} {M δ : ℝ} (hM : 0 ≤ M)
    (hinv : ∀ i j,
      |((roundCylinderGram u (chartAt E₂ z.1)
          (chartAt E₂ z.1 z.1, z.2))⁻¹ i j)| ≤ M)
    (hT : ∀ k ≤ order, ∀ a,
      |roundCylinderIteratedDerivative u (chartAt E₂ z.1) B k
        (chartAt E₂ z.1 z.1, z.2) a| ≤ δ) :
    roundCylinderJetErrorSquared u B order z ≤
      ∑ k ∈ Finset.range (order + 1),
        ((3 : ℝ) ^ (2 + k)) ^ 2 * M ^ (2 + k) * δ ^ 2 := by
  dsimp only [roundCylinderJetErrorSquared]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ order := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact roundCylinderTensorNormSquared_le _ _ _
    (hinv := hinv) (hT := hT k hk') hM

end PoincareConjecture.M34
