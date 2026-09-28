import PoincareConjecture.Proofs.M35.CapGeometry.InitialNeckScalar











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35



theorem exists_initial_axial_scale_control {theta epsilon : ℝ}
    (htheta : theta < 1) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ d : ℝ, 0 < d → d ≤ delta →
      ∀ t ∈ Icc (0 : ℝ) theta,
        ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
          (x : StandardCapSpace) (N : StandardCylinderPatch d⁻¹ x),
          RoundCylinderClose d t (roundCylinderPullback g N.coordinate) →
            let Q := D.scalarCurvature x
            let c := (Real.sqrt Q)⁻¹
            1 / 2 < Q ∧ Q < 3 / (2 * (1 - theta)) ∧
              0 < c ∧ c < 2 ∧ c * epsilon⁻¹ ≤ d⁻¹ ∧ ⌊epsilon⁻¹⌋₊ ≤ ⌊d⁻¹⌋₊ := by
  obtain ⟨dscalar, hdscalar, hcontrol⟩ := exists_initial_cylinder_scalar_control
    htheta (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨min dscalar (epsilon / 4), lt_min hdscalar (by positivity), ?_⟩
  intro d hd hdd t ht g D x N hclose
  obtain ⟨q, hq⟩ := N.center_sphere
  have h := hcontrol d hd (hdd.trans (min_le_left _ _)) t ht g D x N q hclose
  rw [hq] at h
  let Q := D.scalarCurvature x
  let c := (Real.sqrt Q)⁻¹
  have hlo : -(1 / 2 : ℝ) < (1 - t) * Q - 1 := (abs_lt.mp h).1
  have hhi : (1 - t) * Q - 1 < 1 / 2 := (abs_lt.mp h).2
  have htone : t < 1 := ht.2.trans_lt htheta
  have hQ : 0 < Q := by
    have hp : 0 < (1 - t) * Q := by linarith only [hlo]
    exact pos_of_mul_pos_right hp (sub_pos.mpr htone).le
  have hQlo : 1 / 2 < Q := by
    have hmul : (1 - t) * Q ≤ Q := by nlinarith only [ht.1, hQ]
    linarith only [hmul, hlo]
  have hQhi : Q < 3 / (2 * (1 - theta)) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) (sub_pos.mpr htheta))).mpr
    have hmon := mul_le_mul_of_nonneg_right (sub_le_sub_left ht.2 1) hQ.le
    nlinarith only [hhi, hmon]
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hunit : Q * c ^ 2 = 1 := by
    change Q * ((Real.sqrt Q)⁻¹) ^ 2 = 1
    rw [inv_pow, Real.sq_sqrt hQ.le, mul_inv_cancel₀ hQ.ne']
  have hcsmall : c < 2 := by
    have hmul := mul_lt_mul_of_pos_right hQlo (sq_pos_of_pos hc)
    rw [hunit] at hmul
    nlinarith only [hmul, hc]
  have hdsmall : d ≤ epsilon / 4 := hdd.trans (min_le_right _ _)
  have hlength : 4 * epsilon⁻¹ ≤ d⁻¹ := by
    have hh := inv_anti₀ hd hdsmall
    rw [inv_div] at hh
    simpa only [div_eq_mul_inv] using hh
  have heinv : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hfit : c * epsilon⁻¹ ≤ d⁻¹ := by
    have hh := mul_lt_mul_of_pos_right hcsmall heinv
    linarith only [hh, hlength, heinv]
  have horder : epsilon⁻¹ ≤ d⁻¹ := by linarith only [hlength, heinv]
  exact ⟨hQlo, hQhi, hc, hcsmall, hfit, Nat.floor_mono horder⟩

end PoincareConjecture.M35
