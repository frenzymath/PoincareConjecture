import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Covariant
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.ModelConnection

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.EpsilonNeck

section Neck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem normalized_pullback_second_jet_center
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 4 → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    let E := fun (b : Fin 2 → Fin 3) p =>
      roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
    roundCylinderIteratedDerivative 0 c N.normalized_pullback 2 (0, s) a =
      fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
        (roundCylinderCoordinateBasis (a 1))) (0, s)
        (roundCylinderCoordinateBasis (a 0)) -
      ∑ i : Fin 2, ∑ d : Fin 3,
        fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d (a 1)
          (a i.succ.succ)) (0, s) (roundCylinderCoordinateBasis (a 0)) *
            E (Function.update (fun j => a j.succ.succ) i d) (0, s) := by
  classical
  dsimp only
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E := fun (b : Fin 2 → Fin 3) p =>
    roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
  have hE (b : Fin 2 → Fin 3) : ContDiffAt ℝ ∞ (E b) (0, s) := by
    apply ((N.normalized_pullback_close.1 q (b 0) (b 1)).contDiffAt ?_).sub
      (contDiff_roundCylinderGram 0 q (b 0) (b 1)).contDiffAt
    rw [roundCylinder_sphereChart_target]
    exact (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩
  let F := fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
    (roundCylinderCoordinateBasis (a 1))
  have hF : DifferentiableAt ℝ F (0, s) :=
    (((hE _).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  let G := fun (i : Fin 2) (d : Fin 3) p =>
    roundCylinderChristoffel 0 c p d (a 1) (a i.succ.succ)
  let B := fun (i : Fin 2) (d : Fin 3) =>
    E (Function.update (fun j => a j.succ.succ) i d)
  have hG (i : Fin 2) (d : Fin 3) : DifferentiableAt ℝ (G i d) (0, s) :=
    (contDiff_roundCylinderChristoffel (by norm_num) q d (a 1)
      (a i.succ.succ)).differentiable (by simp) (0, s)
  have hB (i : Fin 2) (d : Fin 3) : DifferentiableAt ℝ (B i d) (0, s) :=
    (hE _).differentiableAt (by simp)
  have hsum : DifferentiableAt ℝ (fun p => ∑ i : Fin 2, ∑ d : Fin 3,
      G i d p * B i d p) (0, s) :=
    DifferentiableAt.fun_sum fun i _ =>
      DifferentiableAt.fun_sum fun d _ => (hG i d).mul (hB i d)
  have hd (i : Fin 2) (d : Fin 3) :
      fderiv ℝ (fun p => G i d p * B i d p) (0, s) =
        B i d (0, s) • fderiv ℝ (G i d) (0, s) := by
    rw [fderiv_fun_mul (hG i d) (hB i d)]
    simp only [G, c, roundCylinderChristoffel_center, zero_smul, zero_add]
  change fderiv ℝ (fun p => F p - ∑ i : Fin 2, ∑ d : Fin 3,
      G i d p * B i d p) (0, s) (roundCylinderCoordinateBasis (a 0)) -
      ∑ i : Fin 3, ∑ d : Fin 3,
        roundCylinderChristoffel 0 c (0, s) d (a 0) (a i.succ) *
          roundCylinderIteratedDerivative 0 c N.normalized_pullback 1 (0, s)
            (Function.update (fun j => a j.succ) i d) = _
  simp only [c, roundCylinderChristoffel_center, zero_mul, Finset.sum_const_zero,
    sub_zero]
  rw [fderiv_fun_sub hF hsum]
  simp only [sub_apply]
  congr 1
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun (i : Fin 2) p => ∑ d : Fin 3, G i d p * B i d p)
    (fun i _ => DifferentiableAt.fun_sum fun d _ => (hG i d).mul (hB i d))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun (d : Fin 3) p => G i d p * B i d p)
    (fun d _ => (hG i d).mul (hB i d))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro d _
  rw [hd]
  simp only [smul_apply, smul_eq_mul, G, B, E, c, mul_comm]

private theorem second_derivative_bound_of_model_bound
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (D : ℝ) (hD : 0 ≤ D)
    (hDb : ∀ b d j i : Fin 3,
      |fderiv ℝ (fun p => roundCylinderChristoffel 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p b d j) (0, s)
        (roundCylinderCoordinateBasis i)| ≤ D) (a : Fin 4 → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    let E := fun (b : Fin 2 → Fin 3) p =>
      roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
    |fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
      (roundCylinderCoordinateBasis (a 1))) (0, s)
      (roundCylinderCoordinateBasis (a 0))| ≤ (16 + 24 * D) * N.epsilon := by
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
  have hR (i : Fin 2) (d : Fin 3) : |R i d| ≤ D * (4 * N.epsilon) := by
    dsimp only [R]
    rw [abs_mul]
    exact mul_le_mul (hDb _ _ _ _) (hzero _) (abs_nonneg _) hD
  have hsum : |∑ i : Fin 2, ∑ d : Fin 3, R i d| ≤ 24 * D * N.epsilon := by
    calc
      _ ≤ ∑ i : Fin 2, |∑ d : Fin 3, R i d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, ∑ d : Fin 3, |R i d| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 2, ∑ _d : Fin 3, D * (4 * N.epsilon) :=
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

end Neck

theorem exists_normalized_pullback_second_derivative_center_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ a : Fin 4 → Fin 3,
      let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
      let E := fun (b : Fin 2 → Fin 3) p =>
        roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
      |fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
        (roundCylinderCoordinateBasis (a 1))) (0, s)
        (roundCylinderCoordinateBasis (a 0))| ≤ C * N.epsilon := by
  obtain ⟨D, hD, hDb⟩ := exists_roundCylinderChristoffel_derivative_center_bound
  refine ⟨16 + 24 * D, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ g N q s hs a
  exact second_derivative_bound_of_model_bound N q hs D hD.le (hDb q s) a

end PoincareConjecture.EpsilonNeck
