import PoincareConjecture.Proofs.M47.LimitFiniteLocalSide
import PoincareConjecture.Proofs.M47.LimitFiniteNeckReturn
import PoincareConjecture.Proofs.M47.LimitFiniteNeckExits
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47



theorem limitFinite_captured_neck_impossible
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (hcomplete : MetricComplete g) (hsec : N.connection.NonnegativeSectionalCurvature)
    (hepsilon : N.epsilon ≤ 1 / 100)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcapture : N.carrier ⊆ c.source) {r : ℝ} (hr : 0 < r)
    (htarget : closedBall (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ c.target)
    (hball : c '' N.carrier ⊆ ball 0 r) (o z : M)
    (ho : o ∉ c.symm '' ball 0 r) (hz : z ∉ c.symm '' ball 0 r)
    (hwide : (g.edist N.center o).toReal ^ 2 + (g.edist N.center z).toReal ^ 2 ≤
      (g.edist o z).toReal ^ 2) : False := by
  let := g.toMetricSpace
  have hcenter := N.central_sphere_subset N.center_on_central_sphere
  have hwhole : N.carrier ⊆ c.symm '' ball 0 r := by
    intro x hx
    exact ⟨c x, hball (mem_image_of_mem c hx), c.left_inv (hcapture hx)⟩
  have hneO : N.center ≠ o := fun h => ho (h ▸ hwhole hcenter)
  have hneZ : N.center ≠ z := fun h => hz (h ▸ hwhole hcenter)
  have ha : 0 < (g.edist N.center o).toReal := dist_pos.mpr hneO
  have hb : 0 < (g.edist N.center z).toReal := dist_pos.mpr hneZ
  obtain ⟨gamma, hgamma0, hgammaEnd, hgamma, hgammaSpeed, hgammaMin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hcomplete N.center o ha
  obtain ⟨sigma, hsigma0, hsigmaEnd, hsigma, hsigmaSpeed, hsigmaMin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hcomplete N.center z hb
  have hhalf : N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) ⊆ N.carrier := by
    intro x hx
    have hi := inv_pos.mpr N.epsilon_pos
    exact ((N.mem_coordinate_slab_iff (by linarith) (by linarith)).mp hx).1
  obtain ⟨s, hs, t, ht, hsbound, htbound, hscarrier, htcarrier, _, _, hopposite⟩ :=
    limitFinite_neck_opposite_exits N hcomplete hsec hepsilon ha hb hgamma hsigma
      hgamma0 hsigma0 hgammaSpeed hsigmaSpeed hgammaMin hsigmaMin
      (by rw [hgammaEnd]; exact fun hx => ho (hwhole (hhalf hx)))
      (by rw [hsigmaEnd]; exact fun hx => hz (hwhole (hhalf hx)))
      (by simpa only [hgammaEnd, hsigmaEnd] using hwide)
  obtain ⟨A, hA, _, hAball, hAfront, hAhalf⟩ :=
    limitFinite_neck_local_bounded_side N c hcapture hr htarget
      ((image_mono N.central_sphere_subset).trans hball)
  have hgs := hscarrier ⟨hs.1.le, le_rfl⟩
  have hst := htcarrier ⟨ht.1.le, le_rfl⟩
  have hgammaOut : gamma (g.edist N.center o).toReal ∉ A := by
    rw [hgammaEnd]
    exact fun hx => ho (hAball hx)
  have hsigmaOut : sigma (g.edist N.center z).toReal ∉ A := by
    rw [hsigmaEnd]
    exact fun hx => hz (hAball hx)
  have hreturnGamma (hin : gamma s ∈ A) : False :=
    limitFinite_neck_return_impossible N hA hAfront ⟨hs.1.le, hs.2⟩
      hgamma.contMDiffOn.continuousOn hgamma0 hgammaMin hsbound hin hgammaOut
  have hreturnSigma (hin : sigma t ∈ A) : False :=
    limitFinite_neck_return_impossible N hA hAfront ⟨ht.1.le, ht.2⟩
      hsigma.contMDiffOn.continuousOn hsigma0 hsigmaMin htbound hin hsigmaOut
  rcases hAhalf with hnegative | hpositive
  · by_cases hsign : (N.coordinate_inverse (gamma s)).2 < 0
    · exact hreturnGamma (hnegative
        ⟨hgs, (N.coordinate_inverse_mem _ hgs).2.1, hsign⟩)
    · have hsign' : (N.coordinate_inverse (sigma t)).2 < 0 := by
        by_contra hnot
        exact not_lt_of_ge (mul_nonneg (le_of_not_gt hsign) (le_of_not_gt hnot)) hopposite
      exact hreturnSigma (hnegative
        ⟨hst, (N.coordinate_inverse_mem _ hst).2.1, hsign'⟩)
  · by_cases hsign : 0 < (N.coordinate_inverse (gamma s)).2
    · exact hreturnGamma (hpositive
        ⟨hgs, hsign, (N.coordinate_inverse_mem _ hgs).2.2⟩)
    · have hsign' : 0 < (N.coordinate_inverse (sigma t)).2 := by
        by_contra hnot
        exact not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos
          (le_of_not_gt hsign) (le_of_not_gt hnot)) hopposite
      exact hreturnSigma (hpositive
        ⟨hst, hsign', (N.coordinate_inverse_mem _ hst).2.2⟩)

end PoincareConjecture.M47
