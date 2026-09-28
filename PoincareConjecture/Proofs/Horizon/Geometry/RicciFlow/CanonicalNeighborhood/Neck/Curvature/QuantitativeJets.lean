import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Euclidean
import Mathlib.Analysis.Calculus.Deriv.Inv









noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

namespace PoincareConjecture

private theorem cylinder_factor_fderiv (p v : RoundCylinderCoordinates) :
    fderiv ℝ (fun x : RoundCylinderCoordinates => 32 / (‖x.1‖ ^ 2 + 4) ^ 2) p v =
      (-128 / (‖p.1‖ ^ 2 + 4) ^ 3) * ⟪p.1, v.1⟫_ℝ := by
  have hn := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).hasFDerivAt.norm_sq
    (x := p)
  have ht := (hasDerivAt_const (‖p.1‖ ^ 2) (32 : ℝ)).div
    (((hasDerivAt_id (‖p.1‖ ^ 2)).add_const 4).pow 2)
    (show (‖p.1‖ ^ 2 + 4) ^ 2 ≠ 0 by positivity)
  have hd := (ht.comp_hasFDerivAt p hn).fderiv
  change fderiv ℝ (fun x : RoundCylinderCoordinates => 32 / (‖x.1‖ ^ 2 + 4) ^ 2) p = _ at hd
  rw [hd]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Pi.pow_apply, id_eq]
  change ((0 * (‖p.1‖ ^ 2 + 4) ^ 2 - 32 * (2 * (‖p.1‖ ^ 2 + 4) ^ (2 - 1) * 1)) /
    ((‖p.1‖ ^ 2 + 4) ^ 2) ^ 2) * (2 * ⟪p.1, v.1⟫_ℝ) = _
  field_simp
  ring

theorem fderiv_roundCylinderGram_formula (q : UnitTwoSphere)
    (p v : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fun x => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) p v =
      (-128 / (‖p.1‖ ^ 2 + 4) ^ 3) * ⟪p.1, v.1⟫_ℝ *
        ⟪(roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis b).1⟫_ℝ := by
  have heq : (fun x => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) =
      fun x : RoundCylinderCoordinates =>
        (32 / (‖x.1‖ ^ 2 + 4) ^ 2) *
          ⟪(roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis b).1⟫_ℝ +
          (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 := by
    funext x
    rw [roundCylinderGram_eq_stereographic_formula]
    ring
  rw [heq, fderiv_add_const, fderiv_mul_const]
  simp only [smul_apply, smul_eq_mul, cylinder_factor_fderiv]
  ring
  exact ((contDiff_const.div
    ((((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const).pow 2)
    (fun x => pow_ne_zero 2 (by positivity : ‖x.1‖ ^ 2 + 4 ≠ 0))) :
      ContDiff ℝ ∞ _).differentiable (by simp) p

theorem second_fderiv_roundCylinderGram_center (q : UnitTwoSphere) (s : ℝ)
    (a b : Fin 3) (v w : RoundCylinderCoordinates) :
    fderiv ℝ (fun p => fderiv ℝ (fun x => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) p v) (0, s) w =
      -2 * ⟪w.1, v.1⟫_ℝ *
        ⟪(roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis b).1⟫_ℝ := by
  simp_rw [fderiv_roundCylinderGram_formula]
  let F : RoundCylinderCoordinates → ℝ := fun p => -128 / (‖p.1‖ ^ 2 + 4) ^ 3
  let L : RoundCylinderCoordinates →L[ℝ] ℝ :=
    (innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  have hF : DifferentiableAt ℝ F (0, s) := by
    dsimp [F]
    exact ((contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const).pow 3)
      (fun x => pow_ne_zero 3 (by positivity : ‖x.1‖ ^ 2 + 4 ≠ 0))) :
        ContDiff ℝ ∞ _).differentiable (by simp) (0, s)
  have heq (p : RoundCylinderCoordinates) : ⟪p.1, v.1⟫_ℝ = L p :=
    real_inner_comm _ _
  simp_rw [heq]
  change fderiv ℝ (fun p => F p * L p * _) (0, s) w = _
  rw [fderiv_mul_const, fderiv_fun_mul hF L.differentiableAt]
  simp [F, L, ContinuousLinearMap.fderiv]
  ring
  exact hF.mul L.differentiableAt

theorem abs_second_fderiv_roundCylinderGram_center_le (q : UnitTwoSphere) (s : ℝ)
    (a b i j : Fin 3) :
    |fderiv ℝ (fun p => fderiv ℝ (fun x => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) x a b) p
      (roundCylinderCoordinateBasis j)) (0, s) (roundCylinderCoordinateBasis i)| ≤ 2 := by
  rw [second_fderiv_roundCylinderGram_center]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left]

theorem abs_roundCylinderGram_inv_center_le_one (q : UnitTwoSphere) (s : ℝ)
    (a b : Fin 3) :
    |(roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) (0, s))⁻¹ a b| ≤ 1 := by
  have hg : roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) (0, s) =
      Matrix.diagonal ![(2 : ℝ), 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [roundCylinderGram_eq_stereographic_formula, roundCylinderCoordinateBasis,
        Matrix.diagonal, EuclideanSpace.inner_single_left]
  have hi : (Matrix.diagonal ![(2 : ℝ), 2, 1])⁻¹ =
      Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2, 1] := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [Matrix.diagonal]
  rw [hg, hi]
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.diagonal]

theorem abs_fderiv_roundCylinderChristoffel_center_le_nine (q : UnitTwoSphere) (s : ℝ)
    (a b d i : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)
      (roundCylinderCoordinateBasis i)| ≤ 9 := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let G := fun (j : Fin 3) p => (roundCylinderGram 0 c p)⁻¹ a j
  let F := fun (j k l : Fin 3) p =>
    fderiv ℝ (fun x => roundCylinderGram 0 c x j k) p (roundCylinderCoordinateBasis l)
  let H := fun (j : Fin 3) p => F d j b p + F b j d p - F b d j p
  have hG (j : Fin 3) : DifferentiableAt ℝ (G j) (0, s) :=
    (contDiff_roundCylinderGram_inv (by norm_num) q a j).differentiable (by simp) (0, s)
  have hF (j k l : Fin 3) : DifferentiableAt ℝ (F j k l) (0, s) :=
    (((contDiff_roundCylinderGram 0 q j k).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).differentiable (by simp) (0, s)
  have hH (j : Fin 3) : DifferentiableAt ℝ (H j) (0, s) :=
    ((hF d j b).add (hF b j d)).sub (hF b d j)
  have hH0 (j : Fin 3) : H j (0, s) = 0 := by
    simp [H, F, c, fderiv_roundCylinderGram_center]
  have hDH (j : Fin 3) :
      |fderiv ℝ (H j) (0, s) (roundCylinderCoordinateBasis i)| ≤ 6 := by
    dsimp only [H]
    rw [fderiv_fun_sub ((hF d j b).fun_add (hF b j d)) (hF b d j),
      fderiv_fun_add (hF d j b) (hF b j d)]
    simp only [sub_apply, add_apply]
    have h1 := abs_second_fderiv_roundCylinderGram_center_le q s d j i b
    have h2 := abs_second_fderiv_roundCylinderGram_center_le q s b j i d
    have h3 := abs_second_fderiv_roundCylinderGram_center_le q s b d i j
    exact (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans
      (add_le_add h1 h2)) h3).trans (by norm_num))
  have hsum : DifferentiableAt ℝ (fun p => ∑ j, G j p * H j p) (0, s) :=
    DifferentiableAt.fun_sum fun j _ => (hG j).mul (hH j)
  change |fderiv ℝ (fun p => (1 / 2 : ℝ) * ∑ j, G j p * H j p) (0, s)
    (roundCylinderCoordinateBasis i)| ≤ 9
  rw [fderiv_const_mul hsum, fderiv_fun_sum (u := Finset.univ)
    (A := fun j p => G j p * H j p) (fun j _ => (hG j).mul (hH j))]
  simp only [smul_apply, sum_apply, smul_eq_mul]
  simp_rw [fderiv_fun_mul (hG _) (hH _), hH0, zero_smul, add_zero,
    smul_apply, smul_eq_mul]
  rw [abs_mul]
  calc
    _ ≤ |(1 / 2 : ℝ)| * ∑ j : Fin 3,
        |G j (0, s) * fderiv ℝ (H j) (0, s) (roundCylinderCoordinateBasis i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |(1 / 2 : ℝ)| * ∑ _j : Fin 3, (6 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul (abs_roundCylinderGram_inv_center_le_one q s a j)
        (hDH j) (abs_nonneg _) zero_le_one).trans (by norm_num)
    _ = 9 := by norm_num

theorem norm_lineModelEquiv_symm_le_one :
    ‖(RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ((RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap).opNorm_le_bound
    zero_le_one
  intro x
  rw [one_mul]
  change ‖(Poincare.EuclideanSpace.euclideanTail x, x 0)‖ ≤ ‖x‖
  rw [Prod.norm_def]
  apply max_le
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hx := EuclideanSpace.norm_sq_eq x
    have ht := EuclideanSpace.norm_sq_eq (Poincare.EuclideanSpace.euclideanTail x)
    simp only [Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton,
      Poincare.EuclideanSpace.euclideanTail, WithLp.ofLp_toLp] at hx ht
    change ‖WithLp.toLp 2 (fun i : Fin 2 => x i.succ)‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith only [hx, ht, sq_nonneg ‖x 0‖]
  · exact PiLp.norm_apply_le x 0

theorem roundCylinderEuclideanCoefficients_scalar_fderiv_zero
    (q : UnitTwoSphere) (i j : Fin 3) :
    fderiv ℝ (fun x => roundCylinderEuclideanCoefficients x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0 = 0 := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have heq : (fun x => roundCylinderEuclideanCoefficients x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) =
      (fun p => roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) ∘ T := by
    funext x
    simpa only [Function.comp_def, Prod.mk_zero_zero, zero_add] using
      roundCylinderEuclideanCoefficients_basis q 0 x i j
  rw [heq, fderiv_comp 0
    ((contDiff_roundCylinderGram 0 q i j).differentiable (by simp) _) T.differentiableAt]
  simp only [map_zero, T, show (0 : RoundCylinderCoordinates) = (0, 0) from rfl,
    fderiv_roundCylinderGram_center, ContinuousLinearMap.zero_comp]

theorem roundCylinderEuclideanCoefficients_scalar_second_le
    (q : UnitTwoSphere) (i j : Fin 3) :
    ‖iteratedFDeriv ℝ 2 (fun x => roundCylinderEuclideanCoefficients x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤ 18 := by
  let E := fun p => roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have hEd : DifferentiableAt ℝ (fderiv ℝ E) (0, 0) :=
    ((contDiff_roundCylinderGram 0 q i j).fderiv_right (m := ∞) (by simp)).differentiable
      (by simp) (0, 0)
  have hcomponent (k l : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ E) (0, 0) (roundCylinderCoordinateBasis k)
        (roundCylinderCoordinateBasis l)‖ ≤ 2 := by
    have h := abs_second_fderiv_roundCylinderGram_center_le q 0 i j k l
    change |fderiv ℝ (fun p => fderiv ℝ E p (roundCylinderCoordinateBasis l))
      (0, 0) (roundCylinderCoordinateBasis k)| ≤ 2 at h
    rw [fderiv_clm_apply hEd (differentiableAt_const _)] at h
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, Real.norm_eq_abs] using h
  have hslot (k : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ E) (0, 0) (roundCylinderCoordinateBasis k)‖ ≤ 6 := by
    exact (norm_le_of_cylinder_basis_bound _ (by norm_num) (hcomponent k)).trans_eq
      (by norm_num)
  have htwo : ‖iteratedFDeriv ℝ 2 E (0, 0)‖ ≤ 18 := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    exact (norm_le_of_cylinder_basis_bound _ (by norm_num) hslot).trans_eq (by norm_num)
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have heq : (fun x => roundCylinderEuclideanCoefficients x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) = E ∘ T := by
    funext x
    simpa only [Function.comp_def, E, Prod.mk_zero_zero, zero_add] using
      roundCylinderEuclideanCoefficients_basis q 0 x i j
  rw [heq]
  have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    T E 2 0
  simp only [map_zero] at h
  exact h.trans ((mul_le_mul htwo
    (pow_le_one₀ (norm_nonneg _) norm_lineModelEquiv_symm_le_one)
    (sq_nonneg _) (by norm_num)).trans_eq (by norm_num))

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem normalized_pullback_second_derivative_center_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 4 → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    let E := fun (b : Fin 2 → Fin 3) p =>
      roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
    |fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
      (roundCylinderCoordinateBasis (a 1))) (0, s)
      (roundCylinderCoordinateBasis (a 0))| ≤ 232 * N.epsilon := by
  classical
  dsimp only
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E := fun (b : Fin 2 → Fin 3) p =>
    roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
  let J := fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
    (roundCylinderCoordinateBasis (a 1))) (0, s)
    (roundCylinderCoordinateBasis (a 0))
  let R := fun (i : Fin 2) (d : Fin 3) =>
    fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d (a 1)
      (a i.succ.succ)) (0, s) (roundCylinderCoordinateBasis (a 0)) *
        E (Function.update (fun j => a j.succ.succ) i d) (0, s)
  have hzero (b : Fin 2 → Fin 3) : |E b (0, s)| ≤ 4 * N.epsilon := by
    simpa only [E, c, Nat.add_zero, pow_succ, pow_zero, one_mul, mul_one,
      show (2 : ℝ) * 2 = 4 by norm_num] using
      N.abs_normalized_pullback_covariant_component_center_le q hs
        (k := 0) (Nat.zero_le _) b
  have htwo :
      |roundCylinderIteratedDerivative 0 c N.normalized_pullback 2 (0, s) a| ≤
        16 * N.epsilon := by
    have h := N.abs_normalized_pullback_covariant_component_center_le q hs
      N.two_le_floor_inv_epsilon a
    norm_num only [show (2 : ℝ) ^ (2 + 2) = 16 by norm_num] at h
    exact h
  have hR (i : Fin 2) (d : Fin 3) : |R i d| ≤ 36 * N.epsilon := by
    dsimp only [R]
    rw [abs_mul]
    exact (mul_le_mul (abs_fderiv_roundCylinderChristoffel_center_le_nine q s _ _ _ _)
      (hzero _) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hsum : |∑ i : Fin 2, ∑ d : Fin 3, R i d| ≤ 216 * N.epsilon := by
    calc
      _ ≤ ∑ i : Fin 2, |∑ d : Fin 3, R i d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, ∑ d : Fin 3, |R i d| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 2, ∑ _d : Fin 3, 36 * N.epsilon :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun d _ => hR i d
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
                    Fintype.card_fin, nsmul_eq_mul]; ring
  have heq := N.normalized_pullback_second_jet_center q hs a
  change roundCylinderIteratedDerivative 0 c N.normalized_pullback 2 (0, s) a =
    J - ∑ i : Fin 2, ∑ d : Fin 3, R i d at heq
  have hJ : J = roundCylinderIteratedDerivative 0 c N.normalized_pullback 2
      (0, s) a + ∑ i : Fin 2, ∑ d : Fin 3, R i d := by linarith
  change |J| ≤ _
  rw [hJ]
  exact (abs_add_le _ _).trans ((add_le_add htwo hsum).trans_eq (by ring))

theorem normalized_pullback_scalar_twoJet_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
    ‖iteratedFDeriv ℝ r (fun p =>
      roundCylinderTensorCoefficient N.normalized_pullback
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j)
      (0, s)‖ ≤ 2116 * N.epsilon := by
  have hε := N.epsilon_pos
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback c p i j -
    roundCylinderGram 0 c p i j
  have hN : ContDiffAt ℝ ∞ (fun p =>
      roundCylinderTensorCoefficient N.normalized_pullback c p i j) (0, s) := by
    apply (N.normalized_pullback_close.1 q i j).contDiffAt
    rw [roundCylinder_sphereChart_target]
    exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩
  have hE : ContDiffAt ℝ ∞ E (0, s) :=
    hN.sub (contDiff_roundCylinderGram 0 q i j).contDiffAt
  have hzero : ‖iteratedFDeriv ℝ 0 E (0, s)‖ ≤ 4 * N.epsilon := by
    rw [norm_iteratedFDeriv_zero]
    have h := N.abs_normalized_pullback_covariant_component_center_le q hs
      (k := 0) (Nat.zero_le _) ![i, j]
    norm_num only [Nat.add_zero, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have hfirst_component (k : Fin 3) :
      ‖fderiv ℝ E (0, s) (roundCylinderCoordinateBasis k)‖ ≤ 8 * N.epsilon := by
    dsimp only [E]
    rw [fderiv_fun_sub (hN.differentiableAt (by simp))
      ((contDiff_roundCylinderGram 0 q i j).differentiable (by simp) (0, s)),
      fderiv_roundCylinderGram_center, sub_zero]
    exact N.abs_normalized_pullback_coefficient_derivative_center_le q hs k i j
  have hone : ‖iteratedFDeriv ℝ 1 E (0, s)‖ ≤ 24 * N.epsilon := by
    rw [norm_iteratedFDeriv_one]
    have h := norm_le_of_cylinder_basis_bound (fderiv ℝ E (0, s))
      (show 0 ≤ 8 * N.epsilon by positivity) hfirst_component
    nlinarith
  have hEd : DifferentiableAt ℝ (fderiv ℝ E) (0, s) :=
    (hE.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsecond_component (k l : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ E) (0, s) (roundCylinderCoordinateBasis k)
        (roundCylinderCoordinateBasis l)‖ ≤ 232 * N.epsilon := by
    have h := N.normalized_pullback_second_derivative_center_le q hs ![k, l, i, j]
    change |fderiv ℝ (fun p => fderiv ℝ E p
      (roundCylinderCoordinateBasis l)) (0, s) (roundCylinderCoordinateBasis k)| ≤
        232 * N.epsilon at h
    rw [fderiv_clm_apply hEd (differentiableAt_const _)] at h
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, Real.norm_eq_abs] using h
  have hsecond_slot (k : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ E) (0, s) (roundCylinderCoordinateBasis k)‖ ≤
        3 * (232 * N.epsilon) :=
    norm_le_of_cylinder_basis_bound _ (by positivity) (hsecond_component k)
  have htwo : ‖iteratedFDeriv ℝ 2 E (0, s)‖ ≤ 2088 * N.epsilon := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    have h := norm_le_of_cylinder_basis_bound
      (fderiv ℝ (fderiv ℝ E) (0, s))
      (show 0 ≤ 3 * (232 * N.epsilon) by positivity) hsecond_slot
    nlinarith
  change ‖iteratedFDeriv ℝ r E (0, s)‖ ≤ _
  interval_cases r <;> nlinarith

theorem normalizedEuclideanCoefficients_scalar_twoJet_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
    ‖iteratedFDeriv ℝ r (fun x =>
      N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
      2116 * N.epsilon := by
  have hε := N.epsilon_pos
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let E := fun p => roundCylinderTensorCoefficient N.normalized_pullback
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j
  have heq : (fun x => E ((0, s) + T x)) =ᶠ[𝓝 0]
      (fun x => N.normalizedEuclideanCoefficients q s x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
    filter_upwards [N.normalizedEuclideanCoefficients_basis_eventuallyEq q hs i j]
      with x hx
    dsimp only [E, T]
    rw [hx, roundCylinderEuclideanCoefficients_basis q s]
  rw [← (heq.iteratedFDeriv ℝ r).self_of_nhds]
  have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    T (fun p => E ((0, s) + p)) r 0
  simp only [map_zero, iteratedFDeriv_comp_add_left, add_zero] at h
  have hpow : ‖T.toContinuousLinearMap‖ ^ r ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) norm_lineModelEquiv_symm_le_one
  exact h.trans ((mul_le_mul (N.normalized_pullback_scalar_twoJet_le q hs r hr i j)
    hpow (pow_nonneg (norm_nonneg _) _) (by positivity)).trans_eq (mul_one _))

end EpsilonNeck
end PoincareConjecture
