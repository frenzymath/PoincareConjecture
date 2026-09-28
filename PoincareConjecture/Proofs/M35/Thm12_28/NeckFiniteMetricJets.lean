import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetBoundsAux
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

private theorem coordinateBasis_norm (i : Fin 3) : ‖roundCylinderCoordinateBasis i‖ = 1 := by
  fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]

private theorem model_connection_jet_bound (ell : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Icc (-ell) ell →
      ∀ a b d : Fin 3,
        ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
          roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b d)
            (0, s)‖ ≤ C := by
  classical
  let q0 : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  let K : Set RoundCylinderCoordinates := {0} ×ˢ Icc (-ell) ell
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hbound (i : Fin 3 × Fin 3 × Fin 3) : ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
        roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q0)
          y i.1 i.2.1 i.2.2) p‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    have h := contDiff_roundCylinderChristoffel zero_lt_one q0 i.1 i.2.1 i.2.2
    exact (h.continuous_iteratedFDeriv
      (by exact_mod_cast le_top (a := (r : ℕ∞)))).continuousOn
  choose c hc using hbound
  refine ⟨∑ i, max (c i) 0, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro q s hs a b d
  have heq : (fun y : RoundCylinderCoordinates =>
      roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b d) =
      (fun y : RoundCylinderCoordinates =>
        roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q0) y a b d) := by
    funext y
    rw [roundCylinderChristoffel_eq zero_lt_one, roundCylinderChristoffel_eq zero_lt_one]
  rw [heq]
  exact (hc (a, b, d) (0, s) ⟨mem_singleton 0, hs⟩).trans
    ((le_max_left _ _).trans
      (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ (a, b, d))))

theorem full_neck_covariant_component_jet_bounds
    {epsilon : ℝ} {B : RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose epsilon 0 B) (he : 0 < epsilon)
    (r n : ℕ) (hnr : n + r ≤ ⌊epsilon⁻¹⌋₊) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ a : Fin (2 + n) → Fin 3,
        ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
          roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
            B n y a) (0, s)‖ ≤ C := by
  classical
  let T (n : ℕ) (q : UnitTwoSphere) (a : Fin (2 + n) → Fin 3)
      (y : RoundCylinderCoordinates) :=
    roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) B n y a
  have hT (n : ℕ) (q : UnitTwoSphere) (s : ℝ)
      (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (a : Fin (2 + n) → Fin 3) :
      ContDiffAt ℝ ∞ (T n q a) (0, s) :=
    contDiffAt_roundCylinderIteratedDerivative zero_lt_one q B (0, s)
      (fun i j => hclose.contDiffAt_coefficient q (0, s) hs i j) n a
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ q s, s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
    ∀ a, ‖iteratedFDeriv ℝ r (T n q a) (0, s)‖ ≤ C
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    cases r with
    | zero =>
      refine ⟨(2 : ℝ) ^ (2 + n) * epsilon, by positivity, ?_⟩
      intro q s hs a
      have h := hclose.component_abs_lt he (by norm_num) zero_lt_one
        (z := (q, s)) hs (by omega) a
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, T, sphere_chart_center] using h.le
    | succ r =>
      obtain ⟨Cn, hCn, hnext⟩ := ih r (Nat.lt_succ_self r) (n + 1) (by omega)
      have hprevious (m : Fin (r + 1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q s,
          s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ a,
            ‖iteratedFDeriv ℝ m.1 (T n q a) (0, s)‖ ≤ C :=
        ih m.1 m.2 n (by omega)
      choose c hc using hprevious
      choose G hG using fun m : Fin (r + 1) => model_connection_jet_bound epsilon⁻¹ m.1
      let H : ℝ := ∑ m : Fin (r + 1),
        (r.choose m.1 : ℝ) * G m * c ⟨r - m.1, by omega⟩
      have hH : 0 ≤ H := Finset.sum_nonneg (fun m _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG m).1) (hc _).1)
      let D := Cn + (2 + n) * 3 * H
      have hD : 0 ≤ D := add_nonneg hCn (mul_nonneg (by positivity) hH)
      obtain ⟨K, hK, hKbound⟩ := exists_cylinder_component_norm_bound (r + 1)
      refine ⟨K * D, mul_nonneg hK.le hD, ?_⟩
      intro q s hs a
      apply hKbound _ D hD
      intro v
      let d := v (Fin.last r)
      let aa : Fin (2 + (n + 1)) → Fin 3 := Fin.cons d a
      let J (i : Fin (2 + n)) (j : Fin 3) (y : RoundCylinderCoordinates) :=
        roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          y j d (a i) * T n q (Function.update a i j) y
      have hJ (i : Fin (2 + n)) (j : Fin 3) : ContDiffAt ℝ ∞ (J i j) (0, s) :=
        (contDiff_roundCylinderChristoffel zero_lt_one q j d (a i)).contDiffAt.mul
          (hT n q s hs (Function.update a i j))
      have hJbound (i : Fin (2 + n)) (j : Fin 3) :
          ‖iteratedFDeriv ℝ r (J i j) (0, s)‖ ≤ H := by
        apply (norm_iteratedFDeriv_mul_le_at r
          (contDiff_roundCylinderChristoffel zero_lt_one q j d (a i)).contDiffAt
          (hT n q s hs (Function.update a i j))).trans
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_le_sum
        intro m _
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left ((hG m).2 q s ⟨hs.1.le, hs.2.le⟩ j d (a i))
            (Nat.cast_nonneg _))
          ((hc ⟨r - m.1, by omega⟩).2 q s hs (Function.update a i j))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hG m).1)
      have hrec : (fun y => fderiv ℝ (T n q a) y (roundCylinderCoordinateBasis d)) =
          fun y => T (n + 1) q aa y + ∑ i : Fin (2 + n), ∑ j : Fin 3, J i j y := by
        funext y
        simp only [T, aa, roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
          Fin.cons_zero, Fin.cons_succ, J]
        exact (sub_add_cancel _ _).symm
      have hsum : ContDiffAt ℝ ∞
          (fun y => ∑ i : Fin (2 + n), ∑ j : Fin 3, J i j y) (0, s) :=
        ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => hJ i j))
      have hderiv : ‖iteratedFDeriv ℝ r
          (fun y => fderiv ℝ (T n q a) y (roundCylinderCoordinateBasis d)) (0, s)‖ ≤ D := by
        have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
        rw [hrec, fun_iteratedFDeriv_add_apply ((hT (n + 1) q s hs aa).of_le hr)
          (hsum.of_le hr)]
        apply (norm_add_le _ _).trans
        apply add_le_add (hnext q s hs aa)
        rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
          (ContDiffAt.sum (fun j _ => hJ i j)).of_le hr)]
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _i : Fin (2 + n), ∑ _j : Fin 3, H := by
            apply Finset.sum_le_sum
            intro i _
            rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hJ i j).of_le hr)]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hJbound i j))
          _ = (2 + n) * 3 * H := by simp; ring
      rw [iteratedFDeriv_directional_apply r (hT n q s hs a)]
      have hnorm := (iteratedFDeriv ℝ r
        (fun y => fderiv ℝ (T n q a) y (roundCylinderCoordinateBasis d)) (0, s)).le_opNorm
          (Fin.init (fun j => roundCylinderCoordinateBasis (v j)))
      simp only [Fin.init_def, coordinateBasis_norm, Finset.prod_const_one, mul_one,
        Real.norm_eq_abs] at hnorm
      exact hnorm.trans hderiv

theorem full_neck_metric_error_jet_bounds
    {epsilon : ℝ} {B : RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose epsilon 0 B) (he : 0 < epsilon)
    (r : ℕ) (hr : r ≤ ⌊epsilon⁻¹⌋₊) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
            roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := full_neck_covariant_component_jet_bounds hclose he r 0 (by omega)
  refine ⟨C, hC, ?_⟩
  intro q s hs a b
  exact hbound q s hs ![a, b]

theorem full_neck_metric_coefficient_jet_bounds
    {epsilon : ℝ} {B : RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose epsilon 0 B) (he : 0 < epsilon)
    (r : ℕ) (hr : r ≤ ⌊epsilon⁻¹⌋₊) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b)
            (0, s)‖ ≤ C := by
  classical
  obtain ⟨Ce, hCe, herror⟩ := full_neck_metric_error_jet_bounds hclose he r hr
  let q0 : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  let K : Set RoundCylinderCoordinates := {0} ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have hbound (i : Fin 3 × Fin 3) : ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q0) y i.1 i.2) p‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    have h := contDiff_roundCylinderGram 0 q0 i.1 i.2
    exact (h.continuous_iteratedFDeriv
      (by exact_mod_cast le_top (a := (r : ℕ∞)))).continuousOn
  choose c hc using hbound
  let Cg := ∑ i, max (c i) 0
  have hCg : 0 ≤ Cg := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨Ce + Cg, add_nonneg hCe hCg, ?_⟩
  intro q s hs a b
  let G (y : RoundCylinderCoordinates) :=
    roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b
  have hG : ‖iteratedFDeriv ℝ r G (0, s)‖ ≤ Cg := by
    have heq : G = fun y : RoundCylinderCoordinates =>
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q0) y a b := by
      funext y
      dsimp only [G]
      rw [roundCylinderGram_eq, roundCylinderGram_eq]
    rw [heq]
    exact (hc (a, b) (0, s) ⟨mem_singleton 0, hs.1.le, hs.2.le⟩).trans
      ((le_max_left _ _).trans
        (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ (a, b))))
  have hB := hclose.contDiffAt_coefficient q (0, s) hs a b
  have hGcont := (contDiff_roundCylinderGram 0 q a b).contDiffAt (x := (0, s))
  have hr' : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  have herr := herror q s hs a b
  rw [fun_iteratedFDeriv_sub_apply (hB.of_le hr') (hGcont.of_le hr')] at herr
  exact (norm_le_norm_sub_add _ _).trans (add_le_add herr hG)

end PoincareConjecture.M35
