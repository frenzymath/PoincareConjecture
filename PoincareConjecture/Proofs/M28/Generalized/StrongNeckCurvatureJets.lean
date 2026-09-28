import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderCoefficientBounds











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M28

open PoincareConjecture.Proofs.M28.NeckAnalysis

private theorem half_window_tensor_weight {u : ℝ}
    (hu : u ∈ Icc (-(1 / 2 : ℝ)) 0) {k : ℕ} (hk : k ≤ 2)
    (a : Fin (2 + k) → Fin 3) : (1 / 81 : ℝ) ≤ cylinderTensorWeight u a := by
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  have hinv (j : Fin 3) : (1 / 3 : ℝ) ≤ (cylinderGramDiagonal u j)⁻¹ := by
    have hdiag : cylinderGramDiagonal u j ≤ 3 := by
      fin_cases j <;> dsimp [cylinderGramDiagonal] <;> linarith [hu.1]
    simpa only [one_div] using
      one_div_le_one_div_of_le (cylinderGramDiagonal_pos hu1 j) hdiag
  have hprod : (1 / 3 : ℝ) ^ (2 + k) ≤ cylinderTensorWeight u a := by
    have h := Finset.prod_le_prod
      (fun _ (_ : _ ∈ (Finset.univ : Finset (Fin (2 + k)))) =>
        (by norm_num : (0 : ℝ) ≤ 1 / 3))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 + k)))) => hinv (a i))
    simpa [cylinderTensorWeight] using h
  have hsmall : (1 / 81 : ℝ) ≤ (1 / 3 : ℝ) ^ (2 + k) := by
    interval_cases k <;> norm_num
  exact hsmall.trans hprod


theorem cylinderTensorDerivative_time_eq {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) T =
      roundCylinderTensorDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) T := by
  funext p a
  simp only [roundCylinderTensorDerivative, roundCylinderChristoffel_chosen_chart hu,
    roundCylinderChristoffel_chosen_chart (by norm_num : (0 : ℝ) < 1)]



theorem half_cylinder_covariant_component_le
    {epsilon u : ℝ} (hepsilon : 0 < epsilon)
    (hu : u ∈ Icc (-(1 / 2 : ℝ)) 0) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon u B)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    {k : ℕ} (hk : k ≤ 2) (horder : k ≤ ⌊epsilon⁻¹⌋₊)
    (a : Fin (2 + k) → Fin 3) :
    |roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k (0, z.2) a| ≤ 9 * epsilon := by
  classical
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let T := roundCylinderIteratedDerivative u c B k (0, z.2)
  obtain ⟨bound, hbound, henergy⟩ := hB.2
  have horderBound : roundCylinderTensorNormSquared u c (0, z.2) T < epsilon ^ 2 := by
    have hsingle := Finset.single_le_sum
      (f := fun j => roundCylinderTensorNormSquared u c (c z.1, z.2)
        (roundCylinderIteratedDerivative u c B j (c z.1, z.2)))
      (fun j _ => roundCylinderTensorNormSquared_nonneg hu1 z _)
      (Finset.mem_range.mpr (by omega : k < ⌊epsilon⁻¹⌋₊ + 1))
    have h := hsingle.trans_lt ((henergy z hz).trans_lt hbound)
    rw [show c z.1 = 0 from sphere_chart_center z.1] at h
    exact h
  have hsquare : cylinderTensorWeight u a * T a ^ 2 ≤
      roundCylinderTensorNormSquared u c (0, z.2) T := by
    have h := roundCylinderTensorNormSquared_eq_sum hu1 z T
    rw [sphere_chart_center] at h
    rw [h]
    exact Finset.single_le_sum
      (fun b _ => mul_nonneg (cylinderTensorWeight_pos hu1 b).le (sq_nonneg _))
      (Finset.mem_univ a)
  have hlower := mul_le_mul_of_nonneg_right (half_window_tensor_weight hu hk a)
    (sq_nonneg (T a))
  have hsq : |T a| ^ 2 ≤ (9 * epsilon) ^ 2 := by
    rw [sq_abs]
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsq



theorem half_cylinder_first_component_le
    {epsilon u : ℝ} (hepsilon : 0 < epsilon)
    (hu : u ∈ Icc (-(1 / 2 : ℝ)) 0) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon u B)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (horder : 1 ≤ ⌊epsilon⁻¹⌋₊) (a : Fin 2 → Fin 3) (i : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0 p a)
      (0, z.2) (roundCylinderCoordinateBasis i)| ≤ 9 * epsilon := by
  have h := half_cylinder_covariant_component_le hepsilon hu hB hz
    (by omega : 1 ≤ 2) horder (Fin.cons i a)
  change |roundCylinderTensorDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (roundCylinderIteratedDerivative u
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0)
      (0, z.2) (Fin.cons i a)| ≤ 9 * epsilon at h
  rw [cylinderTensorDerivative_time_eq (lt_of_le_of_lt hu.2 (by norm_num)),
    roundCylinderTensorDerivative_center] at h
  exact h



theorem exists_half_cylinder_second_component_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (epsilon u : ℝ), 0 < epsilon →
      u ∈ Icc (-(1 / 2 : ℝ)) 0 →
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon u B →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      2 ≤ ⌊epsilon⁻¹⌋₊ → ∀ (a : Fin 2 → Fin 3) (i j : Fin 3),
        |fderiv ℝ (fun p => fderiv ℝ (fun y =>
          roundCylinderIteratedDerivative u
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0 y a) p
          (roundCylinderCoordinateBasis i)) (0, z.2) (roundCylinderCoordinateBasis j)| ≤
          L * epsilon := by
  obtain ⟨C, hC, hG⟩ := tube.exists_bound_roundCylinderChristoffel_fderiv
  refine ⟨9 + 54 * C, by positivity, ?_⟩
  intro epsilon u hepsilon hu B hB z hz horder a i j
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let T := roundCylinderIteratedDerivative u c B 0
  have hp : (0, z.2) ∈ c.target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    rw [← sphere_chart_center z.1]
    exact c.map_source (mem_chart_source _ z.1)
  have hT (b : Fin 2 → Fin 3) : ContDiffAt ℝ ∞ (fun p => T p b) (0, z.2) :=
    (contDiffOn_roundCylinderIteratedDerivative hu1 hB.1 z.1 0 b).contDiffAt
      ((c.open_target.prod isOpen_Ioo).mem_nhds hp)
  have hzero (b : Fin 2 → Fin 3) : |T (0, z.2) b| ≤ 9 * epsilon :=
    half_cylinder_covariant_component_le (k := 0) hepsilon hu hB hz
      (by omega) (by omega) b
  have hsecond := half_cylinder_covariant_component_le hepsilon hu hB hz
    (by omega : 2 ≤ 2) horder (Fin.cons j (Fin.cons i a))
  change |roundCylinderTensorDerivative u c
      (roundCylinderTensorDerivative u c T) (0, z.2) (Fin.cons j (Fin.cons i a))| ≤
    9 * epsilon at hsecond
  simp only [c, cylinderTensorDerivative_time_eq hu1] at hsecond
  have hGpoint (b : Fin 2) (d : Fin 3) :
      |fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d i (a b))
        (0, z.2) (roundCylinderCoordinateBasis j)| ≤ C := by
    calc
      _ = ‖fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d i (a b))
          (0, z.2) (roundCylinderCoordinateBasis j)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d i (a b))
          (0, z.2)‖ * ‖roundCylinderCoordinateBasis j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by
        rw [norm_roundCylinderCoordinateBasis, mul_one]
        exact hG 0 (by norm_num) z.1 z.2 d i (a b)
  let P := fun (b : Fin 2) (d : Fin 3) =>
    fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d i (a b))
      (0, z.2) (roundCylinderCoordinateBasis j) * T (0, z.2) (Function.update a b d)
  have hP (b : Fin 2) (d : Fin 3) : ‖P b d‖ ≤ C * (9 * epsilon) := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGpoint b d) (hzero _) (abs_nonneg _) hC
  have hsum : |∑ b : Fin 2, ∑ d : Fin 3, P b d| ≤ 6 * (C * (9 * epsilon)) := by
    calc
      _ = ‖∑ b : Fin 2, ∑ d : Fin 3, P b d‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ b : Fin 2, ‖∑ d : Fin 3, P b d‖ := norm_sum_le _ _
      _ ≤ ∑ _b : Fin 2, ∑ _d : Fin 3, C * (9 * epsilon) := by
        apply Finset.sum_le_sum
        intro b _
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => hP b d))
      _ = _ := by simp; ring
  change |fderiv ℝ (fun p => fderiv ℝ (fun y => T y a) p
    (roundCylinderCoordinateBasis i)) (0, z.2) (roundCylinderCoordinateBasis j)| ≤ _
  rw [second_fderiv_cylinder_component z.1 z.2 T hT]
  have h := (abs_add_le
    (roundCylinderTensorDerivative 0 c (roundCylinderTensorDerivative 0 c T)
      (0, z.2) (Fin.cons j (Fin.cons i a)))
    (∑ b : Fin 2, ∑ d : Fin 3, P b d)).trans (add_le_add hsecond hsum)
  calc
    _ ≤ 9 * epsilon + 6 * (C * (9 * epsilon)) := h
    _ = (9 + 54 * C) * epsilon := by ring

end PoincareConjecture.M28
