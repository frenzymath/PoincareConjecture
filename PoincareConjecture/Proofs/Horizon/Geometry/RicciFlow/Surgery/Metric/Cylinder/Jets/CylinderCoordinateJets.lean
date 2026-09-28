import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderJetComponents










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.MetricSurgery

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "C" => RoundCylinderCoordinates

theorem roundCylinderTensorDerivative_center (theta : UnitTwoSphere) (s : ℝ)
    {r : ℕ} (T : C → (Fin r → Fin 3) → ℝ) (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative 0 (chartAt E₂ theta) T (0, s) a =
      fderiv ℝ (fun p => T p (fun i => a i.succ)) (0, s)
        (roundCylinderCoordinateBasis (a 0)) := by
  simp only [roundCylinderTensorDerivative, roundCylinderChristoffel_center,
    zero_mul, Finset.sum_const_zero, sub_zero]

theorem roundCylinderTensorDerivative_center_fderiv (theta : UnitTwoSphere) (s : ℝ)
    {r : ℕ} (T : C → (Fin r → Fin 3) → ℝ)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun p => T p a) (0, s))
    (a : Fin (r + 1) → Fin 3) (v : C) :
    fderiv ℝ (fun p => roundCylinderTensorDerivative 0 (chartAt E₂ theta) T p a) (0, s) v =
      fderiv ℝ (fun p => fderiv ℝ (fun q => T q (fun i => a i.succ)) p
        (roundCylinderCoordinateBasis (a 0))) (0, s) v -
      ∑ i : Fin r, ∑ j : Fin 3,
        fderiv ℝ (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p
          j (a 0) (a i.succ)) (0, s) v *
          T (0, s) (Function.update (fun k => a k.succ) i j) := by
  have hlead : DifferentiableAt ℝ
      (fun p => fderiv ℝ (fun q => T q (fun i => a i.succ)) p
        (roundCylinderCoordinateBasis (a 0))) (0, s) :=
    (((hT _).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hG (i : Fin r) (j : Fin 3) : DifferentiableAt ℝ
      (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p j (a 0) (a i.succ))
      (0, s) :=
    (roundCylinderChristoffel_chart_contDiff theta j (a 0) (a i.succ)).differentiable
      (by simp) _
  have hprod (i : Fin r) (j : Fin 3) : DifferentiableAt ℝ
      (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p j (a 0) (a i.succ) *
        T p (Function.update (fun k => a k.succ) i j)) (0, s) :=
    (hG i j).mul ((hT _).differentiableAt (by simp))
  have hsum (i : Fin r) := DifferentiableAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hprod i j)
  unfold roundCylinderTensorDerivative
  rw [fderiv_fun_sub hlead (DifferentiableAt.fun_sum (fun i _ => hsum i)),
    fderiv_fun_sum (fun i _ => hsum i)]
  simp only [sub_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_sum (fun j _ => hprod i j)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (hG i j) ((hT _).differentiableAt (by simp))]
  simp only [roundCylinderChristoffel_center, zero_smul,
    smul_apply, smul_eq_mul, zero_add]
  ring

theorem roundCylinder_metric_error_contDiffAt {epsilon : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin 2 → Fin 3) :
    ContDiffAt ℝ ∞
      (fun p => roundCylinderIteratedDerivative 0 (chartAt E₂ z.1) B 0 p a) (0, z.2) := by
  have hc : (0 : E₂) ∈ (chartAt E₂ z.1).target := by
    rw [← sphere_chart_center_zero z.1]
    exact (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have hopen : IsOpen ((chartAt E₂ z.1).target ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    (chartAt E₂ z.1).open_target.prod isOpen_Ioo
  have hmem : (0, z.2) ∈
      (chartAt E₂ z.1).target ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ := ⟨hc, hz⟩
  have hco := (hB.1 z.1 (a 0) (a 1)).contDiffAt (hopen.mem_nhds hmem)
  exact hco.sub (roundCylinderGram_chart_contDiff z.1 (a 0) (a 1)).contDiffAt

theorem roundCylinderClose_first_coordinate_error {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (horder : 1 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (i a b : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderTensorCoefficient B (chartAt E₂ z.1) p a b -
      roundCylinderGram 0 (chartAt E₂ z.1) p a b) (0, z.2)
        (roundCylinderCoordinateBasis i)| ≤ 3 * epsilon := by
  have h := roundCylinderClose_first_component hepsilon hB horder z hz ![i, a, b]
  rw [sphere_chart_center_zero] at h
  change |roundCylinderTensorDerivative 0 (chartAt E₂ z.1)
    (roundCylinderIteratedDerivative 0 (chartAt E₂ z.1) B 0) (0, z.2) ![i, a, b]| ≤ _ at h
  rw [roundCylinderTensorDerivative_center] at h
  exact h

theorem roundCylinderClose_second_coordinate_error {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (k i a b : Fin 3) :
    |fderiv ℝ (fun p => fderiv ℝ
        (fun q => roundCylinderTensorCoefficient B (chartAt E₂ z.1) q a b -
          roundCylinderGram 0 (chartAt E₂ z.1) q a b) p
        (roundCylinderCoordinateBasis i)) (0, z.2)
      (roundCylinderCoordinateBasis k)| ≤ 10 * epsilon := by
  let T := roundCylinderIteratedDerivative 0 (chartAt E₂ z.1) B 0
  let U : Fin 3 → Fin 3 := ![i, a, b]
  let correction := ∑ l : Fin 2, ∑ j : Fin 3,
    fderiv ℝ (fun p => roundCylinderChristoffel 0 (chartAt E₂ z.1) p
      j (U 0) (U l.succ)) (0, z.2) (roundCylinderCoordinateBasis k) *
      T (0, z.2) (Function.update (fun m => U m.succ) l j)
  let ordinary := fderiv ℝ
    (fun p => fderiv ℝ (fun q => T q (fun m => U m.succ)) p
      (roundCylinderCoordinateBasis (U 0))) (0, z.2) (roundCylinderCoordinateBasis k)
  have h2 := roundCylinderClose_second_component hepsilon hB horder z hz ![k, i, a, b]
  rw [sphere_chart_center_zero] at h2
  change |roundCylinderTensorDerivative 0 (chartAt E₂ z.1)
    (roundCylinderTensorDerivative 0 (chartAt E₂ z.1) T) (0, z.2) ![k, i, a, b]| ≤ _ at h2
  rw [roundCylinderTensorDerivative_center] at h2
  change |fderiv ℝ (fun p => roundCylinderTensorDerivative 0 (chartAt E₂ z.1) T p U)
    (0, z.2) (roundCylinderCoordinateBasis k)| ≤ _ at h2
  rw [roundCylinderTensorDerivative_center_fderiv z.1 z.2 T
    (roundCylinder_metric_error_contDiffAt hB z hz) U] at h2
  change |ordinary - correction| ≤ 4 * epsilon at h2
  have h0 (c : Fin 2 → Fin 3) : |T (0, z.2) c| ≤ 2 * epsilon := by
    have hc := roundCylinderClose_derivative_component hepsilon hB (Nat.zero_le _) z hz c
    rw [sphere_chart_center_zero] at hc
    norm_num at hc
    have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simpa only [T, hsqrt] using hc
  have hterm (l : Fin 2) (j : Fin 3) :
      |fderiv ℝ (fun p => roundCylinderChristoffel 0 (chartAt E₂ z.1) p
        j (U 0) (U l.succ)) (0, z.2) (roundCylinderCoordinateBasis k) *
        T (0, z.2) (Function.update (fun m => U m.succ) l j)| ≤ epsilon := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 2 : ℝ) * (2 * epsilon) :=
        mul_le_mul (roundCylinderChristoffel_center_derivative_bound z.1 z.2 _ _ _ k)
          (h0 _) (abs_nonneg _) (by norm_num)
      _ = epsilon := by ring
  have hcorr : |correction| ≤ 6 * epsilon := by
    calc
      |correction| ≤ ∑ l : Fin 2, ∑ j : Fin 3,
          |fderiv ℝ (fun p => roundCylinderChristoffel 0 (chartAt E₂ z.1) p
            j (U 0) (U l.succ)) (0, z.2) (roundCylinderCoordinateBasis k) *
            T (0, z.2) (Function.update (fun m => U m.succ) l j)| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        exact Finset.sum_le_sum (fun l _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _l : Fin 2, ∑ _j : Fin 3, epsilon :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun j _ => hterm l j
      _ = 6 * epsilon := by simp; ring
  change |ordinary| ≤ 10 * epsilon
  rcases abs_le.mp h2 with ⟨hlo, hhi⟩
  rcases abs_le.mp hcorr with ⟨hclo, hchi⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PoincareConjecture.MetricSurgery
