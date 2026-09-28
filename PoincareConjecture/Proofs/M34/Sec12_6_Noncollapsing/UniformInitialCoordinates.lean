import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.ReferenceDiffeomorph
import PoincareConjecture.Proofs.M34.Standard.CenteredCoordinates
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EnergyCutoffs
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M34

theorem uniform_initial_coordinates_of_cylindrical_end
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g) :
    ∃ delta b j : ℝ, 0 < delta ∧ 0 < b ∧ 0 < j ∧ ∀ q : StandardCapSpace,
      ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
        f 0 = q ∧ Metric.ball 0 (2 * delta) ⊆ f.source ∧
        ∀ z ∈ Metric.ball 0 (2 * delta),
          ‖M10.pullbackMetricForm g f z‖ ≤ b ∧ j ≤ M10.pullbackJacobian g f z := by
  let C : Set StandardCapSpace := {q | endExhaustion e q ≤ 4}
  let S := endReferenceSection e
  have hC : IsCompact C := endExhaustion_sublevel_isCompact e 4
  have hS : IsCompact S := endReferenceSection_isCompact e
  obtain ⟨eta, heta, hmargin⟩ := hS.exists_cthickening_subset_open
    (endReferenceRegion_isOpen e) (endReferenceSection_subset_region e)
  let delta : ℝ := eta / 4
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let K : Set StandardCapSpace := Metric.cthickening eta (C ∪ S)
  have hK : IsCompact K := (hC.union hS).cthickening
  obtain ⟨b, j, hb, hj, hbound⟩ := compact_identity_metric_bounds g hK
  have hshift (A : Set StandardCapSpace) (x z : StandardCapSpace) (hx : x ∈ A)
      (hz : z ∈ Metric.ball 0 (2 * delta)) : x + z ∈ Metric.cthickening eta A := by
    apply Metric.mem_cthickening_of_dist_le (x + z) x eta A hx
    have hn : ‖z‖ < 2 * delta := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [dist_eq_norm]
    simpa only [add_sub_cancel_left] using (show ‖z‖ ≤ eta by dsimp [delta] at hn; linarith)
  refine ⟨delta, b, j, hdelta, hb, hj, fun q => ?_⟩
  have hchart : ∃ x ∈ C ∪ S,
      ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
        f 0 = q ∧ Metric.ball 0 (2 * delta) ⊆ f.source ∧
        ∀ z ∈ Metric.ball 0 (2 * delta),
          M10.pullbackMetricForm g f z = M10.pullbackMetricForm g id (x + z) := by
    by_cases hq : q ∈ C
    · let f := (modelTranslationDiffeomorph (𝕜 := ℝ) q).toPartialDiffeomorph
      refine ⟨q, Or.inl hq, f, ?_, subset_univ _, fun z _ => ?_⟩
      · change q + 0 = q
        exact add_zero q
      · convert! modelTranslationDiffeomorph_pullbackMetricForm g q z using 1
    · have hlarge : 4 < endExhaustion e q := lt_of_not_ge hq
      obtain ⟨w, _hw, hcoord, hrho⟩ := endExhaustion_large_coordinate e (by linarith)
      have hH : 3 ≤ w.2 := by linarith
      obtain ⟨x, hx, hcenter⟩ := endTranslation_covers_tail e w
      let d := endReferenceDiffeomorph e hH
      let f := centeredDiffeomorph d x
      have hsource (z : StandardCapSpace) (hz : z ∈ Metric.ball 0 (2 * delta)) :
          x + z ∈ endReferenceRegion e := hmargin (hshift S x z hx hz)
      refine ⟨x, Or.inr hx, f, ?_, ?_, fun z hz => ?_⟩
      · change endAxialTranslation e (w.2 - 4) (x + 0) = q
        simpa only [add_zero] using hcenter.trans hcoord
      · intro z hz
        exact (centeredDiffeomorph_mem_source d x z).mpr (hsource z hz)
      · exact (centeredDiffeomorph_pullbackMetricForm g d x z (hsource z hz)).trans
          (endReferenceDiffeomorph_pullback e hH (hsource z hz))
  obtain ⟨x, hx, f, hcenter, hsource, hform⟩ := hchart
  refine ⟨f, hcenter, hsource, fun z hz => ?_⟩
  have hxz : x + z ∈ K := hshift (C ∪ S) x z hx hz
  have hjac : M10.pullbackJacobian g f z = M10.pullbackJacobian g id (x + z) := by
    simp only [M10.pullbackJacobian, hform z hz]
  rw [hform z hz, hjac]
  exact hbound (x + z) hxz

theorem uniform_initial_coordinate_volume
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g) :
    ∃ delta b v : ℝ, 0 < delta ∧ 0 < b ∧ 0 < v ∧ ∀ q : StandardCapSpace,
      ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
        f 0 = q ∧ Metric.ball 0 (2 * delta) ⊆ f.source ∧
        (∀ z ∈ Metric.ball 0 (2 * delta), ‖M10.pullbackMetricForm g f z‖ ≤ b) ∧
        ∀ r ∈ Ioc 0 delta, ENNReal.ofReal (v * r ^ 3) ≤
          calibratedMetricVolume g (f '' Metric.ball 0 r) := by
  obtain ⟨delta, b, j, hdelta, hb, hj, hcharts⟩ :=
    uniform_initial_coordinates_of_cylindrical_end e
  refine ⟨delta, b, j * (Real.pi * 4 / 3), hdelta, hb, by positivity, fun q => ?_⟩
  obtain ⟨f, hf0, hsource, hbounds⟩ := hcharts q
  refine ⟨f, hf0, hsource, fun z hz => (hbounds z hz).1, fun r hr => ?_⟩
  have hball : Metric.ball (0 : StandardCapSpace) r ⊆ Metric.ball 0 (2 * delta) :=
    Metric.ball_subset_ball (by linarith [hr.2])
  have hvol := coordinate_ball_volume_lower g f (hball.trans hsource)
    (fun z hz => (hbounds z (hball hz)).2)
  rw [EuclideanSpace.volume_ball_fin_three] at hvol
  calc
    ENNReal.ofReal (j * (Real.pi * 4 / 3) * r ^ 3) =
        ENNReal.ofReal j * (ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hj.le (by positivity)),
        ENNReal.ofReal_mul hj.le, ENNReal.ofReal_pow hr.1.le]
      ac_rfl
    _ ≤ _ := hvol

end PoincareConjecture.M34
