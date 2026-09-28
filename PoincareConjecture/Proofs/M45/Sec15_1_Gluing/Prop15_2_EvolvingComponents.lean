import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Comparison
import PoincareConjecture.Proofs.M36.CylinderAllOrderBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M45

open M36 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem evolvingCylinderInverseWeight_lower {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 0)
    (i : Fin 3) : (1 / 4 : ℝ) ≤ evolvingCylinderInverseWeight t i := by
  have hp : 0 < 2 * (1 - t) := by linarith [ht.2]
  have hb : (1 / 4 : ℝ) ≤ (2 * (1 - t))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hp]
    linarith [ht.1]
  fin_cases i
  · exact hb
  · exact hb
  · norm_num [evolvingCylinderInverseWeight]

theorem evolvingTensorNormSquared_controls_component {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 0) {r : ℕ}
    (q : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) (a : Fin r → Fin 3) :
    (T a) ^ 2 ≤ (4 : ℝ) ^ r * roundCylinderTensorNormSquared t
      (chartAt E₂ q) (chartAt E₂ q q, s) T := by
  have hweight : (1 / 4 : ℝ) ^ r ≤ ∏ i, evolvingCylinderInverseWeight t (a i) := by
    calc
      (1 / 4 : ℝ) ^ r = ∏ _i : Fin r, (1 / 4 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun i _ => evolvingCylinderInverseWeight_lower ht (a i))
  have hbound : (1 / 4 : ℝ) ^ r * (T a) ^ 2 ≤
      roundCylinderTensorNormSquared t (chartAt E₂ q) (chartAt E₂ q q, s) T := by
    rw [evolving_roundCylinderTensorNormSquared_center (ht.2.trans_lt (by norm_num))]
    apply (mul_le_mul_of_nonneg_right hweight (sq_nonneg _)).trans
    apply Finset.single_le_sum _ (Finset.mem_univ a)
    intro b _
    exact mul_nonneg (Finset.prod_nonneg fun i _ =>
      (by linarith [evolvingCylinderInverseWeight_lower ht (b i)])) (sq_nonneg _)
  calc
    (T a) ^ 2 = (4 : ℝ) ^ r * ((1 / 4 : ℝ) ^ r * (T a) ^ 2) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

theorem evolving_derivative_norm_le_jet {t : ℝ} (ht : t < 1)
    (B : RoundCylinderTwoTensor) {k order : ℕ} (hk : k ≤ order)
    (z : RoundCylinderSpace) :
    roundCylinderTensorNormSquared t (chartAt E₂ z.1)
      (chartAt E₂ z.1 z.1, z.2)
      (roundCylinderIteratedDerivative t (chartAt E₂ z.1) B k
        (chartAt E₂ z.1 z.1, z.2)) ≤ roundCylinderJetErrorSquared t B order z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.single_le_sum (f := fun j =>
    roundCylinderTensorNormSquared t (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2)
      (roundCylinderIteratedDerivative t (chartAt E₂ z.1) B j
        (chartAt E₂ z.1 z.1, z.2)))
  · intro j _
    exact evolvingTensorNormSquared_nonneg ht z.1 z.2 _
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)

theorem correctedCylinderComponent_bound {epsilon t : ℝ} (hepsilon : 0 ≤ epsilon)
    (ht : t ∈ Set.Icc (-1 : ℝ) 0) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon t B) {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin (2 + k) → Fin 3) :
    ‖centeredCylinderComponent (staticCylinderCorrection t B) z.1 z.2 k a 0‖ ≤
      (2 : ℝ) ^ (2 + k) * epsilon := by
  have ht1 : t < 1 := ht.2.trans_lt (by norm_num)
  obtain ⟨bound, hbound, hjet⟩ := hB.2
  have hs := (evolvingTensorNormSquared_controls_component ht z.1 z.2
    (roundCylinderIteratedDerivative t (chartAt E₂ z.1) B k
      (chartAt E₂ z.1 z.1, z.2)) a).trans
    (mul_le_mul_of_nonneg_left
      ((evolving_derivative_norm_le_jet ht1 B hk z).trans ((hjet z hz).trans hbound.le))
      (by positivity))
  simp only [centeredCylinderComponent, staticCylinderCorrection_iteratedDerivative ht1,
    map_zero, zero_add, Real.norm_eq_abs]
  rw [sphere_chart_center_zero] at hs
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (2 : ℝ) ^ (2 + k) * epsilon)).mp
  rw [sq_abs, mul_pow, ← pow_mul, mul_comm (2 + k) 2, pow_mul]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  exact hs

theorem correctedCylinderComponent_contDiffAt {epsilon t : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn epsilon B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (centeredCylinderComponent (staticCylinderCorrection t B)
      z.1 z.2 k a) 0 := by
  induction k with
  | zero =>
      have hc : (0 : E₂) ∈ (chartAt E₂ z.1).target := by
        rw [← sphere_chart_center_zero z.1]
        exact (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
      have hp : (chartAt E₂ z.1).target ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ ∈
          𝓝 ((0 : E₂), z.2) :=
        ((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds ⟨hc, hz⟩
      have hb := (hB z.1 (a 0) (a 1)).contDiffAt hp
      have hgram := (evolving_roundCylinderGram_contDiff t z.1 (a 0) (a 1)).contDiffAt
        (x := ((0 : E₂), z.2))
      have ha : ContDiffAt ℝ ∞
          (fun p : E₃ => cylinderEuclideanEquiv p + (0, z.2)) 0 :=
        cylinderEuclideanEquiv.contDiff.contDiffAt.add contDiffAt_const
      have heq : centeredCylinderComponent (staticCylinderCorrection t B) z.1 z.2 0 a =
          fun p : E₃ => roundCylinderTensorCoefficient B (chartAt E₂ z.1)
            (cylinderEuclideanEquiv p + (0, z.2)) (a 0) (a 1) -
            roundCylinderGram t (chartAt E₂ z.1)
              (cylinderEuclideanEquiv p + (0, z.2)) (a 0) (a 1) := by
        funext p
        simp only [centeredCylinderComponent, roundCylinderIteratedDerivative,
          staticCylinderCorrection_coefficient]
        ring
      rw [heq]
      have hd : ContDiffAt ℝ ∞ (fun p =>
          roundCylinderTensorCoefficient B (chartAt E₂ z.1) p (a 0) (a 1) -
            roundCylinderGram t (chartAt E₂ z.1) p (a 0) (a 1))
          (cylinderEuclideanEquiv 0 + (0, z.2)) := by
        simpa only [map_zero, zero_add] using hb.sub hgram
      exact hd.comp 0 ha
  | succ k ih =>
      rw [show centeredCylinderComponent (staticCylinderCorrection t B) z.1 z.2 (k + 1) a =
          fun p => fderiv ℝ (centeredCylinderComponent (staticCylinderCorrection t B)
            z.1 z.2 k (fun l => a l.succ)) p
              (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)) -
            ∑ l : Fin (2 + k), ∑ b : Fin 3,
              centeredCylinderChristoffel b (a 0) (a l.succ) p *
                centeredCylinderComponent (staticCylinderCorrection t B) z.1 z.2 k
                  (Function.update (fun m => a m.succ) l b) p from
        funext (centeredCylinderComponent_succ _ z.1 z.2 k a)]
      apply ContDiffAt.sub
      · exact ((ih _).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
      · exact ContDiffAt.sum fun l _ => ContDiffAt.sum fun b _ =>
          (centeredCylinderChristoffel_contDiff b (a 0) (a l.succ)).contDiffAt.mul (ih _)

end PoincareConjecture.M45
