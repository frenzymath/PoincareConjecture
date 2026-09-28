import PoincareConjecture.Proofs.M35.CapGeometry.RadialCoreScalarWitness
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCollarPoint
import PoincareConjecture.Proofs.M35.CapGeometry.CurvatureRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness

variable (P : M35StandardCapPredecessors) (g : RiemannianMetric 3 StandardCapSpace)
  (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)

include P hrotation hcomplete

theorem closure_ball_subset_tip_ball (y : StandardCapSpace) {b R : ℝ}
    (hb : 0 ≤ b) (hmargin : radialArclength g ‖y‖ + b < R) :
    closure (g.ball y b) ⊆ g.ball 0 R := by
  have hy : 0 ≤ radialArclength g ‖y‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg y)
  have hcontinuous : Continuous (fun z : StandardCapSpace => g.edist y z) :=
    (@continuous_edist StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace).comp
      (continuous_const.prodMk continuous_id)
  have hclosed : closure (g.ball y b) ⊆ {z | g.edist y z ≤ ENNReal.ofReal b} :=
    closure_minimal (by
      intro z hz
      change g.edist y z < ENNReal.ofReal b at hz
      exact hz.le) (isClosed_le hcontinuous continuous_const)
  intro z hz
  change g.edist 0 z < ENNReal.ofReal R
  calc
    g.edist 0 z ≤ g.edist 0 y + g.edist y z :=
      @edist_triangle StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace 0 y z
    _ ≤ g.edist 0 y + ENNReal.ofReal b := add_le_add_right (hclosed hz) _
    _ = ENNReal.ofReal (radialArclength g ‖y‖ + b) := by
      rw [edist_zero_eq_radialArclength g hrotation hcomplete P,
        ENNReal.ofReal_add hy hb]
    _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg hy hb)).mpr
      hmargin

include D hsec in

theorem radial_core_curvature_balls {a length : ℝ} (ha : 0 < a) (hlength : 0 < length)
    (hfar : 6 * intrinsicWarpingRadius g hrotation hcomplete a < a)
    (hwidth : intrinsicWarpingRadius g hrotation hcomplete a < 2 * length)
    (hR : Continuous D.scalarCurvature) (y : StandardCapSpace)
    (hy : radialArclength g ‖y‖ < a - length) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 3 * intrinsicWarpingRadius g hrotation hcomplete a ∧
      scalarCurvatureSupOn g D (g.ball y r) = r⁻¹ ^ 2 ∧
      closure (g.ball y r) ⊆ g.ball 0 (a + length) ∧
      IsCompact (closure (g.ball y r)) := by
  let f := intrinsicWarpingRadius g hrotation hcomplete a
  have hf : 0 < f := intrinsicWarpingRadius_pos g hrotation hcomplete ha
  have hsy : 0 ≤ radialArclength g ‖y‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg y)
  have hwitness : ∃ b : ℝ, 0 < b ∧ b ≤ 3 * f ∧
      radialArclength g ‖y‖ + b < a + length ∧
      ∃ z ∈ g.ball y b, 1 ≤ b ^ 2 * D.scalarCurvature z := by
    by_cases houter : 2 * f ≤ radialArclength g ‖y‖
    · have hscalar := radial_core_scalar_witness P g D hrotation hcomplete hsec ha y
        houter (by linarith only [hy, hlength])
      refine ⟨f, hf, by linarith only [hf], by linarith only [hy, hwidth], y, ?_, hscalar⟩
      change g.edist y y < ENNReal.ofReal f
      have hself : g.edist y y = 0 :=
        @edist_self StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace y
      rw [hself]
      exact ENNReal.ofReal_pos.mpr hf
    · have hsy' : radialArclength g ‖y‖ < 2 * f := lt_of_not_ge houter
      obtain ⟨z, hz, hzy⟩ := exists_intrinsic_collar_point g hrotation hcomplete P y
        (by positivity : 0 < 2 * f)
      have hzscalar := radial_core_scalar_witness P g D hrotation hcomplete hsec ha z
        (by rw [hz]) (by rw [hz]; linarith only [hfar, hf])
      have hzball : z ∈ g.ball y (3 * f) := by
        apply hzy.trans_lt
        rw [abs_of_pos (sub_pos.mpr hsy')]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 3 * f)).mpr
          (by linarith only [hsy, hf])
      refine ⟨3 * f, by positivity, le_rfl, by linarith only [hsy', hfar, hf, hlength],
        z, hzball, ?_⟩
      have hscaled := mul_le_mul_of_nonneg_left hzscalar (by norm_num : (0 : ℝ) ≤ 9)
      nlinarith only [hscaled]
  obtain ⟨b, hb, hbf, hmargin, z, hz, hcross⟩ := hwitness
  have hcompact := Proofs.M09.isCompact_closure_metric_ball g hcomplete y b
  have hbounded : BddAbove (range fun w : g.ball y b => D.scalarCurvature w.1) := by
    rw [← image_eq_range]
    exact (hcompact.bddAbove_image hR.continuousOn).mono (image_mono subset_closure)
  have hsup : D.scalarCurvature z ≤ scalarCurvatureSupOn g D (g.ball y b) :=
    le_csSup hbounded ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨r, hr, hrb, hscale, hcompactr⟩ := exists_scalar_curvature_radius_le g D hcomplete
    hR y hb (hcross.trans (mul_le_mul_of_nonneg_left hsup (sq_nonneg b)))
  refine ⟨r, hr, hrb.trans hbf, hscale, ?_, hcompactr⟩
  exact (closure_mono (fun w hw => hw.trans_le (ENNReal.ofReal_le_ofReal hrb))).trans
    (closure_ball_subset_tip_ball P g hrotation hcomplete y hb.le hmargin)

end PoincareConjecture.M35.Uniqueness
