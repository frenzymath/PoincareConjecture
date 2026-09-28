import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthBounds
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthError
import PoincareConjecture.Proofs.M13.Metric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47

variable {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
  {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
  (N : StandardEvolvingNeck atlas G v gamma z
    (Icc (-v * (G.connection v).scalarCurvature z) 0))



theorem standard_initial_neck_birth_close :
    RoundCylinderClose gamma (-v * (G.connection v).scalarCurvature z)
      (roundCylinderPullback
        (M13.scaleSmoothMetric g0.metric ((G.connection v).scalarCurvature z) N.scalar_pos)
        N.patch.coordinate) := by
  let R := (G.connection v).scalarCurvature z
  have hR : 0 < R := N.scalar_pos
  have hu : -v * R ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr N.time_mem.1) hR.le
  have hbirth : -v * R ∈ Icc (-v * R) 0 := ⟨le_rfl, hu⟩
  have htime : v + (-v * R) / R = 0 := by
    field_simp [hR.ne']
    ring
  have hinitial : G.metric 0 = g0.metric := G.base.initial_metric
  obtain ⟨hsmooth, B, hB, hjets⟩ := N.close
  have h : RoundCylinderClose gamma (-v * R)
      (fun p a b => R * roundCylinderPullback (G.metric (v + (-v * R) / R))
        N.patch.coordinate p a b) :=
    ⟨hsmooth (-v * R) hbirth, B, hB, hjets (-v * R) hbirth⟩
  change RoundCylinderClose gamma (-v * R)
    (fun p a b => R * roundCylinderPullback g0.metric N.patch.coordinate p a b)
  simpa only [htime, hinitial] using h

section CoordinateNorm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem standard_initial_neck_birth_pullback_bounds
    (hsmall : gamma ≤ 1 / 1200)
    (hdisjoint : Disjoint N.patch.carrier
      {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
    (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-gamma⁻¹) gamma⁻¹)
    (w : EuclideanSpace ℝ (Fin 3)) :
    (20 / 29 : ℝ) ^ 2 * ‖w‖ ^ 2 ≤
        g0.metric.pullbackCoefficients (N.patch.coordinate ∘ M35.cylinderChart q)
          (M35.cylinderCoordinateEquiv.symm (0, s)) w w ∧
      g0.metric.pullbackCoefficients (N.patch.coordinate ∘ M35.cylinderChart q)
          (M35.cylinderCoordinateEquiv.symm (0, s)) w w ≤
        (51 / 50 : ℝ) ^ 2 * M35.cylinderEuclideanCoefficients 0
          (M35.cylinderCoordinateEquiv.symm (0, s)) w w := by
  let R := (G.connection v).scalarCurvature z
  let d := v * R
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  let B := g0.metric.pullbackCoefficients (N.patch.coordinate ∘ M35.cylinderChart q) p w w
  let C := M35.cylinderEuclideanCoefficients (-d) p w w
  let C0 := M35.cylinderEuclideanCoefficients 0 p w w
  have hR : 0 < R := N.scalar_pos
  have hd : 0 ≤ d := mul_nonneg N.time_mem.1 hR.le
  have hu : -d ∈ Icc (-2 : ℝ) 0 := by
    constructor
    · dsimp only [d, R]
      nlinarith only [hshort, hsmall]
    · exact neg_nonpos.mpr hd
  obtain ⟨hRlower, hRupper, hRinv, hRsphere⟩ :=
    standard_initial_neck_birth_scale_bounds N hsmall hdisjoint hshort
  change (99 / 100 : ℝ) < R at hRlower
  change R < (81 / 40 : ℝ) at hRupper
  change 1 / R ≤ (101 / 100 : ℝ) at hRinv
  change (1 + d) / R ≤ (101 / 100 : ℝ) at hRsphere
  let gR := M13.scaleSmoothMetric g0.metric R hR
  have hclose : RoundCylinderClose gamma (-d)
      (roundCylinderPullback gR N.patch.coordinate) := by
    simpa only [neg_mul] using standard_initial_neck_birth_close N
  have hlower := standard_initial_patch_pullback_lower_sharp N.patch gR
    N.epsilon_pos hsmall hu hclose q s hs w
  change (197 / 200 : ℝ) * ‖w‖ ^ 2 ≤ R * B at hlower
  have hB : 0 ≤ B := by nlinarith [sq_nonneg ‖w‖]
  have hupperR : R * B ≤ (81 / 40 : ℝ) * B :=
    mul_le_mul_of_nonneg_right hRupper.le hB
  constructor
  · change (20 / 29 : ℝ) ^ 2 * ‖w‖ ^ 2 ≤ B
    nlinarith [sq_nonneg ‖w‖]
  · have herr := standard_initial_patch_pullback_error_le N.patch gR N.epsilon_pos
      hu hclose q s hs w
    change |R * B - C| ≤ 18 * gamma * ‖w‖ ^ 2 at herr
    have hC0 : ‖w‖ ^ 2 ≤ C0 :=
      M35.cylinderEuclideanCoefficients_lower (u := 0) le_rfl s w
    have hC0pos : 0 ≤ C0 := (sq_nonneg _).trans hC0
    have hmodel : C ≤ (101 / 100 : ℝ) * R * C0 := by
      have haxial : 1 ≤ (101 / 100 : ℝ) * R := (div_le_iff₀ hR).mp hRinv
      have hsphere : 1 + d ≤ (101 / 100 : ℝ) * R :=
        (div_le_iff₀ hR).mp hRsphere
      have hfirst := mul_le_mul_of_nonneg_right hsphere
        (sq_nonneg ‖(M35.cylinderCoordinateEquiv w).1‖)
      have hlast := mul_le_mul_of_nonneg_right haxial
        (sq_nonneg (M35.cylinderCoordinateEquiv w).2)
      dsimp only [C, C0, p]
      simp only [M35.cylinderEuclideanCoefficients_apply,
        ContinuousLinearEquiv.apply_symm_apply, norm_zero, real_inner_self_eq_norm_sq]
      norm_num
      nlinarith
    have hbudget : 18 * gamma * ‖w‖ ^ 2 ≤ (3 / 200 : ℝ) * C0 :=
      (mul_le_mul_of_nonneg_right (by linarith : 18 * gamma ≤ (3 / 200 : ℝ))
        (sq_nonneg _)).trans (mul_le_mul_of_nonneg_left hC0 (by norm_num))
    have hmodelLower : (99 / 100 : ℝ) * C0 ≤ R * C0 :=
      mul_le_mul_of_nonneg_right hRlower.le hC0pos
    have hupper := (abs_le.mp herr).2
    have hscaled : R * B ≤ R * ((51 / 50 : ℝ) ^ 2 * C0) := by nlinarith
    change B ≤ (51 / 50 : ℝ) ^ 2 * C0
    exact (mul_le_mul_iff_right₀ hR).mp hscaled

end CoordinateNorm

end PoincareConjecture.M47
