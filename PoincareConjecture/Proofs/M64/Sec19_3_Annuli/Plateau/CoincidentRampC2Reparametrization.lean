import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CoincidentDegreeOneRamps












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem degreeOneRamp_phase_homeomorph_C2
    (P : M62.CircleProductData F circumference) {gamma : ℝ → P.charts.Point}
    (L : M63PositiveDegreeLift P gamma) (hdegree : L.degree = 1) :
    ∃ phi : ℝ ≃ₜ ℝ,
      (∀ x, phi x = curvePeriod / circumference * L.lift x) ∧
      ContDiff ℝ 2 (phi : ℝ → ℝ) ∧ ContDiff ℝ 2 (phi.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv phi x) ∧ (∀ x, 0 < deriv phi.symm x) ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      (∀ x, phi.symm (x + curvePeriod) = phi.symm x + curvePeriod) ∧
      ∃ K J : ℝ≥0, LipschitzWith K phi ∧ LipschitzWith J phi.symm := by
  let k := curvePeriod / circumference
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hk : 0 < k := div_pos hP P.circle.positive
  have hd (x : ℝ) : HasDerivAt (fun y => k * L.lift y) (k * deriv L.lift x) x :=
    ((L.regular.differentiable (by norm_num)) x).hasDerivAt.const_mul k
  have hdc : Continuous (fun x => k * deriv L.lift x) :=
    continuous_const.mul (L.regular.continuous_deriv (by norm_num))
  have hpositive (x : ℝ) : 0 < k * deriv L.lift x := mul_pos hk (L.derivative_positive x)
  have hshift (x : ℝ) : k * L.lift (x + curvePeriod) = k * L.lift x + curvePeriod := by
    rw [L.period_shift, hdegree, Nat.cast_one, one_mul, mul_add]
    have hkP : k * circumference = curvePeriod := div_mul_cancel₀ _ P.circle.positive.ne'
    rw [hkP]
  obtain ⟨phi, heq, -, -, -, -, hp, hpi, hdi, K, J, hK, hJ⟩ :=
    M64Uniformization.exists_positive_degree_one_homeomorph hd hdc hpositive hP hshift
  have hphi2 : ContDiff ℝ 2 (phi : ℝ → ℝ) := by
    rw [heq]
    exact contDiff_const.mul L.regular
  have hphiD (x : ℝ) : HasDerivAt phi (k * deriv L.lift x) x := by
    rw [heq]
    exact hd x
  have hphiI2 : ContDiff ℝ 2 (phi.symm : ℝ → ℝ) :=
    phi.contDiff_symm_deriv (fun x => (hpositive x).ne') hphiD hphi2
  refine ⟨phi, fun x => congrFun heq x, hphi2, hphiI2, ?_, ?_, hp, hpi, K, J, hK, hJ⟩
  · intro x
    rw [(hphiD x).deriv]
    exact hpositive x
  · intro x
    rw [(hdi x).deriv]
    exact inv_pos.mpr (hpositive _)



theorem coincident_degreeOneRamps_reparametrize_C2
    (P : M62.CircleProductData F circumference) {gamma0 gamma1 : ℝ → P.charts.Point}
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (L0 : M63PositiveDegreeLift P gamma0) (L1 : M63PositiveDegreeLift P gamma1)
    (hd0 : L0.degree = 1) (hd1 : L1.degree = 1)
    (himage : range gamma0 = range gamma1) :
    ∃ phi : ℝ ≃ₜ ℝ,
      ContDiff ℝ 2 (phi : ℝ → ℝ) ∧ (∀ x, 0 < deriv phi x) ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      (∀ x, gamma0 (phi x) = gamma1 x) ∧
      ∃ K : ℝ≥0, LipschitzWith K phi := by
  obtain ⟨phi0, he0, -, hci0, -, hdi0, -, hpi0, K0, J0, -, hJ0⟩ :=
    degreeOneRamp_phase_homeomorph_C2 P L0 hd0
  obtain ⟨phi1, he1, hc1, -, hd1', -, hp1, -, K1, J1, hK1, -⟩ :=
    degreeOneRamp_phase_homeomorph_C2 P L1 hd1
  let phi := phi1.trans phi0.symm
  have hC : ContDiff ℝ 2 (phi : ℝ → ℝ) := hci0.comp hc1
  have hD (x : ℝ) : 0 < deriv phi x := by
    have hcomp := ((hci0.differentiable (by norm_num)) (phi1 x)).hasDerivAt.comp x
      ((hc1.differentiable (by norm_num)) x).hasDerivAt
    change HasDerivAt phi _ x at hcomp
    rw [hcomp.deriv]
    exact mul_pos (hdi0 _) (hd1' _)
  refine ⟨phi, hC, hD, ?_, ?_, J0 * K1, hJ0.comp hK1⟩
  · intro x
    change phi0.symm (phi1 (x + curvePeriod)) = phi0.symm (phi1 x) + curvePeriod
    rw [hp1, hpi0]
  · intro x
    have hscale : 0 < curvePeriod / circumference :=
      div_pos (by unfold curvePeriod; positivity) P.circle.positive
    have hphase : L0.lift (phi x) = L1.lift x := by
      apply mul_left_cancel₀ hscale.ne'
      calc
        curvePeriod / circumference * L0.lift (phi x) = phi0 (phi x) := (he0 _).symm
        _ = phi1 x := phi0.apply_symm_apply _
        _ = curvePeriod / circumference * L1.lift x := he1 x
    obtain ⟨y, hy⟩ := (show gamma1 x ∈ range gamma0 by rw [himage]; exact mem_range_self x)
    have hcircle : (gamma0 (phi x)).2 = (gamma0 y).2 := by
      rw [← L0.quotient_eq, hphase, L1.quotient_eq, hy]
    exact (degreeOneRamp_eq_of_circle_eq P hp0 L0 hd0 hcircle).trans hy

end PoincareConjecture.M64
