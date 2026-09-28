import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialInterval
import PoincareConjecture.Proofs.M47.CanonicalNeckScalarComparison
import PoincareConjecture.Proofs.M35.RawFlow.InitialCylinderCoordinates
import PoincareConjecture.Proofs.M36.CylindricalBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M47

open Proofs.M47

theorem standard_initial_scalar_eq_one_of_tip_distance
    (g0 : StandardInitialMetric) {x : StandardCapSpace}
    (hx : ENNReal.ofReal g0.cylindrical_end.radius < g0.metric.edist 0 x) :
    g0.connection.scalarCurvature x = 1 := by
  have hrad : g0.cylindrical_end.radius < M36.radialArclength g0 ‖x‖ := by
    by_contra hn
    apply (not_le_of_gt hx)
    rw [M36.standard_edist_zero]
    exact ENNReal.ofReal_le_ofReal (le_of_not_gt hn)
  have hmem : x ∈ g0.cylindrical_end.carrier := by
    rw [M36.cylindrical_carrier_eq]
    exact hrad.le
  have hheight := g0.cylindrical_end.inverse_domain x hmem
  have hpositive : 0 < (g0.cylindrical_end.inverse x).2 := by
    by_contra hn
    have hzero : (g0.cylindrical_end.inverse x).2 = 0 :=
      le_antisymm (le_of_not_gt hn) hheight
    have heq : g0.cylindrical_end.coordinate
        ((g0.cylindrical_end.inverse x).1, 0) = x := by
      simpa only [← hzero] using g0.cylindrical_end.coordinate_right_inverse hmem
    have hboundary := M36.cylindrical_zero_radial g0 (g0.cylindrical_end.inverse x).1
    rw [heq] at hboundary
    exact hrad.ne hboundary.symm
  have hscalar := (M35.Uniqueness.initialEnd_scalar_norm g0.cylindrical_end
    g0.connection (g0.cylindrical_end.inverse x).1 hpositive).1
  change g0.connection.scalarCurvature
    (g0.cylindrical_end.coordinate (g0.cylindrical_end.inverse x)) = 1 at hscalar
  rwa [g0.cylindrical_end.coordinate_right_inverse hmem] at hscalar

theorem standard_initial_neck_birth_scale_lt_four
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z
      (Icc (-v * (G.connection v).scalarCurvature z) 0))
    (hsmall : gamma ≤ 1 / 200)
    (hdisjoint : Disjoint N.patch.carrier
      {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
    (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma) :
    |1 / (G.connection v).scalarCurvature z -
        1 / (1 + v * (G.connection v).scalarCurvature z)| ≤ (16 / 5 : ℝ) * gamma ∧
      (G.connection v).scalarCurvature z < 4 := by
  let q := (G.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  have hv : 0 ≤ v := N.time_mem.1
  have hu : -v * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) hq.le
  have hzero : (0 : ℝ) ∈ Icc (-v * q) 0 := ⟨hu, le_rfl⟩
  let K := (N.staticAtZero hzero).toEpsilonNeck
  have hz : z ∈ K.carrier := K.central_sphere_subset K.center_on_central_sphere
  have hfar : ENNReal.ofReal (g0.cylindrical_end.radius + 4) < g0.metric.edist 0 z := by
    apply lt_of_not_ge
    intro h
    exact Set.disjoint_left.mp hdisjoint hz h
  have hscalar0 : g0.connection.scalarCurvature z = 1 :=
    standard_initial_scalar_eq_one_of_tip_distance g0
      ((ENNReal.ofReal_le_ofReal (by linarith :
        g0.cylindrical_end.radius ≤ g0.cylindrical_end.radius + 4)).trans_lt hfar)
  have hbirth : -v * q ∈ Icc (-v * q) 0 := ⟨le_rfl, hu⟩
  have htime : v + (-v * q) / q = 0 := by
    field_simp [hq.ne']
    ring
  have hinitial : G.metric 0 = g0.metric := G.base.initial_metric
  have hclose : RoundCylinderClose gamma (-v * q)
      (fun p a b => q * roundCylinderPullback g0.metric K.coordinate_map p a b) := by
    obtain ⟨hsmooth, B, hB, hjets⟩ := N.close
    have h : RoundCylinderClose gamma (-v * q)
        (fun p a b => q * roundCylinderPullback (G.metric (v + (-v * q) / q))
          K.coordinate_map p a b) :=
      ⟨hsmooth (-v * q) hbirth, B, hB, hjets (-v * q) hbirth⟩
    simpa only [htime, hinitial] using h
  have herror := neck_pullback_scalar_difference_le K hsmall
    g0.metric g0.connection hq hu hclose z hz
  rw [hscalar0] at herror
  change |1 / q - 1 / (1 - (-v * q))| ≤ (16 / 5 : ℝ) * gamma at herror
  have herror' : |1 / q - 1 / (1 + v * q)| ≤ (16 / 5 : ℝ) * gamma := by
    simpa only [neg_mul, sub_neg_eq_add] using herror
  refine ⟨herror', ?_⟩
  have hden : 0 < 1 + v * q := by nlinarith [mul_nonneg hv hq.le]
  have hdenUpper : 1 + v * q < 5 / 2 := by linarith only [hshort, hsmall]
  have hreciprocal : (2 / 5 : ℝ) < 1 / (1 + v * q) := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden).mpr
    linarith only [hdenUpper]
  have herrorUpper : (16 / 5 : ℝ) * gamma ≤ 2 / 125 := by
    linarith only [hsmall]
  have hinverse : (1 / 4 : ℝ) < 1 / q := by
    have h := (abs_le.mp herror').1
    linarith only [h, hreciprocal, herrorUpper]
  have hproduct := (lt_div_iff₀ hq).mp hinverse
  change q < 4
  linarith only [hproduct]

end PoincareConjecture.M47
