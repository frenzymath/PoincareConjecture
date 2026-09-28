import PoincareConjecture.Proofs.M35.Thm12_28.CylinderOrdinaryJets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

theorem roundCylinderInverseWeight_lower {u : ℝ} (hlo : -1 ≤ u) (hu : u < 1)
    (a : Fin 3) :
    (1 / 4 : ℝ) ≤ ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] a := by
  have h : (1 / 4 : ℝ) ≤ (2 * (1 - u))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (a := 2 * (1 - u)) (b := 4) (by linarith) (by linarith)
  fin_cases a <;> first | exact h | norm_num

private theorem basis_inner_abs_le (a b : Fin 3) :
    |inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1| ≤ 1 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left]

theorem abs_fderiv_roundCylinderChristoffel_center_le {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (i a b d : Fin 3) :
    |fderiv ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d)
      (0, s) (roundCylinderCoordinateBasis i)| ≤ 3 / 2 := by
  have hprod (a b c d : Fin 3) :
      |inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 *
        inner ℝ (roundCylinderCoordinateBasis c).1 (roundCylinderCoordinateBasis d).1| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (basis_inner_abs_le a b) (basis_inner_abs_le c d)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  rw [fderiv_roundCylinderChristoffel_center hu, abs_mul]
  have hsum := (abs_sub
    (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1 *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis b).1 +
      inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis d).1)
    (inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1 *
      inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis a).1)).trans
        (add_le_add (abs_add_le _ _) le_rfl)
  have h1 := hprod a d i b
  have h2 := hprod a b i d
  have h3 := hprod b d i a
  norm_num
  linarith

end PoincareConjecture.M35

namespace PoincareConjecture.RoundCylinderClose

theorem component_abs_lt {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (he : 0 < epsilon)
    (hlo : -1 ≤ u) (hu : u < 1)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊) (a : Fin (2 + k) → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
    |roundCylinderIteratedDerivative u c B k (c z.1, z.2) a| <
      (2 : ℝ) ^ (2 + k) * epsilon := by
  dsimp only
  let T := roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
    B k (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a
  have hw : (1 / 4 : ℝ) ^ (2 + k) ≤
      ∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i) := by
    calc
      _ = ∏ _ : Fin (2 + k), (1 / 4 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun i _ => M35.roundCylinderInverseWeight_lower hlo hu (a i))
  have hb : (1 / 4 : ℝ) ^ (2 + k) * T ^ 2 < epsilon ^ 2 :=
    (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_lt (h.component_sq_lt hu hz hk a)
  have hp : (1 / 4 : ℝ) ^ (2 + k) * ((2 : ℝ) ^ (2 + k)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (2 + k) 2, pow_mul, ← mul_pow]
    norm_num
  have hp' : (1 / 4 : ℝ) ^ (2 + k) * ((2 : ℝ) ^ (2 + k) * epsilon) ^ 2 =
      epsilon ^ 2 := by rw [mul_pow, ← mul_assoc, hp, one_mul]
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  have hpos := pow_pos (by norm_num : (0 : ℝ) < 1 / 4) (2 + k)
  nlinarith

theorem first_component_abs_lt {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (he : 0 < epsilon)
    (hlo : -1 ≤ u) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hk : 1 ≤ ⌊epsilon⁻¹⌋₊) (a : Fin 3 → Fin 3) :
    |fderiv ℝ (fun p : RoundCylinderCoordinates => roundCylinderTensorCoefficient B
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) (0, s)
        (roundCylinderCoordinateBasis (a 0))| < 8 * epsilon := by
  have hjet := h.component_abs_lt he hlo hu (z := (q, s)) hs hk a
  dsimp only at hjet
  rw [M35.sphere_chart_center] at hjet
  rw [M35.roundCylinderIteratedDerivative_one_center u q s B a
    ((h.contDiffAt_coefficient q (0, s) hs (a 1) (a 2)).differentiableAt (by simp))]
    at hjet
  norm_num at hjet
  exact hjet

theorem second_error_component_abs_lt {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (he : 0 < epsilon)
    (hlo : -1 ≤ u) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hk : 2 ≤ ⌊epsilon⁻¹⌋₊) (a : Fin 4 → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    |fderiv ℝ (fun p => fderiv ℝ (fun x : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B c x (a 2) (a 3) - roundCylinderGram u c x (a 2) (a 3))
        p (roundCylinderCoordinateBasis (a 1))) (0, s)
          (roundCylinderCoordinateBasis (a 0))| < 52 * epsilon := by
  dsimp only
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E0 := roundCylinderIteratedDerivative u c B 0 (0, s)
  let term (i : Fin 2) (j : Fin 3) : ℝ :=
    fderiv ℝ (fun p => roundCylinderChristoffel u c p j (a 1) (a i.succ.succ))
      (0, s) (roundCylinderCoordinateBasis (a 0)) *
        E0 (Function.update (fun k : Fin 2 => a k.succ.succ) i j)
  have hzero (b : Fin 2 → Fin 3) : |E0 b| ≤ 4 * epsilon := by
    have hb := h.component_abs_lt he hlo hu (z := (q, s)) hs (Nat.zero_le _) b
    dsimp only at hb
    rw [M35.sphere_chart_center] at hb
    norm_num at hb
    exact hb.le
  have htwo : |roundCylinderIteratedDerivative u c B 2 (0, s) a| < 16 * epsilon := by
    have hb := h.component_abs_lt he hlo hu (z := (q, s)) hs hk a
    dsimp only at hb
    rw [M35.sphere_chart_center] at hb
    norm_num at hb
    exact hb
  have hterm (i : Fin 2) (j : Fin 3) : |term i j| ≤ 6 * epsilon := by
    dsimp only [term]
    rw [abs_mul]
    calc
      _ ≤ (3 / 2) * (4 * epsilon) := mul_le_mul
        (M35.abs_fderiv_roundCylinderChristoffel_center_le hu q s (a 0) j (a 1)
          (a i.succ.succ)) (hzero _) (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsum : |∑ i : Fin 2, ∑ j : Fin 3, term i j| ≤ 36 * epsilon := by
    calc
      _ ≤ ∑ i : Fin 2, |∑ j : Fin 3, term i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 2, ∑ _ : Fin 3, 6 * epsilon := Finset.sum_le_sum (fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hterm i j)))
      _ = _ := by norm_num; ring
  let D := fderiv ℝ (fun p => fderiv ℝ (fun x : RoundCylinderCoordinates =>
    roundCylinderTensorCoefficient B c x (a 2) (a 3) - roundCylinderGram u c x (a 2) (a 3))
      p (roundCylinderCoordinateBasis (a 1))) (0, s) (roundCylinderCoordinateBasis (a 0))
  have hid : roundCylinderIteratedDerivative u c B 2 (0, s) a =
      D - ∑ i : Fin 2, ∑ j : Fin 3, term i j :=
    M35.roundCylinderIteratedDerivative_two_center hu q s B
      (fun a b => h.contDiffAt_coefficient q (0, s) hs a b) a
  change |D| < 52 * epsilon
  have hD : D = roundCylinderIteratedDerivative u c B 2 (0, s) a +
      ∑ i : Fin 2, ∑ j : Fin 3, term i j := by linarith
  rw [hD]
  exact (abs_add_le _ _).trans_lt (by linarith)

end PoincareConjecture.RoundCylinderClose
