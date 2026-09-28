import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Ellipticity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Covering
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.DistanceLower

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

theorem eventually_exists_uniform_exponential_cover
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    ∃ R ρ a b : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ 0 < a ∧ 0 < b ∧
      ∃ N : ℕ, ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∃ S : Finset C.carrier,
        F.base ∈ S ∧ (↑S : Set C.carrier) ⊆ F.zeroBall A ∧ S.card ≤ N ∧
        ∃ Φ : S → PartialDiffeomorph (𝓡 n) (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) C.carrier ∞,
          (∀ p, (Φ p).source = Metric.ball 0 R ∧
            (Φ p).target = (F.metricAt 0).ball p R ∧ Φ p 0 = p ∧
            ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
              (∀ a b, (F.metricAt 0).pullbackCoefficients
                (extChartAt (𝓡 n) (p : C.carrier)).symm
                (extChartAt (𝓡 n) (p : C.carrier) p) (L a) (L b) = inner ℝ a b) ∧
              HasFDerivAt (fun w => extChartAt (𝓡 n) (p : C.carrier) (Φ p w))
                L.toContinuousLinearMap 0 ∧
              (∀ w ∈ Metric.ball 0 R,
                (F.metricAt 0).IsGeodesicOn (fun t => Φ p (t • w))
                  {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
              (∀ w ∈ Metric.ball 0 R,
                (F.metricAt 0).edist p (Φ p w) = ENNReal.ofReal ‖w‖) ∧
              ∀ t ∈ Ioo T' T, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v,
                a * ‖v‖ ^ 2 ≤ (F.metricAt t).pullbackCoefficients (Φ p) x v v ∧
                (F.metricAt t).pullbackCoefficients (Φ p) x v v ≤ b * ‖v‖ ^ 2) ∧
          (∀ p, ∀ x ∈ Metric.ball 0 (ρ / 2), ∀ y ∈ Metric.ball 0 (ρ / 2),
            Real.sqrt a * dist x y ≤ ((F.metricAt 0).edist (Φ p x) (Φ p y)).toReal ∧
            ((F.metricAt 0).edist (Φ p x) (Φ p y)).toReal ≤ Real.sqrt b * dist x y) ∧
          (∀ p, IsCompact ((Φ p) '' Metric.closedBall 0 (ρ / 4))) ∧
          F.zeroBall A ⊆ ⋃ p, (Φ p) '' Metric.closedBall 0 (ρ / 4) := by
  classical
  obtain ⟨R, ρ, a, b, hρ, hρR, ha, hb, hcharts⟩ :=
    H.eventually_uniform_elliptic_exponential_charts hn hA
  obtain ⟨N, hcover⟩ := H.eventually_exists_uniform_finset_cover hA
    (by positivity : 0 < ρ / 4)
  refine ⟨R, ρ, a, b, hρ, hρR, ha, hb, N + 1, ?_⟩
  filter_upwards [hcharts, hcover] with k hkcharts hkcover
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : T3Space C.carrier := C.t3Space
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  obtain ⟨S₀, hS₀, hcard, hcover₀⟩ := hkcover
  let S : Finset C.carrier := insert F.base S₀
  have hbase : F.base ∈ F.zeroBall A := by
    change (F.metricAt 0).edist F.base F.base < ENNReal.ofReal A
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hA
  have hS : (↑S : Set C.carrier) ⊆ F.zeroBall A := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hbase
    · exact hS₀ hp
  choose L Φ hsource htarget hzero hL hderiv hgeo hdist hbounds using
    fun p : S => hkcharts p (hS p.property)
  dsimp only
  refine ⟨S, Finset.mem_insert_self _ _, hS,
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hcard 1), Φ, ?_, ?_, ?_, ?_⟩
  · intro p
    exact ⟨hsource p, htarget p, hzero p, L p, hL p, hderiv p, hgeo p, hdist p, hbounds p⟩
  · intro p x hx y hy
    apply (F.metricAt 0).toReal_edist_bounds_of_normal_pullback_bounds p (Φ p)
      (by positivity) (by linarith) ha hb.le (hsource p) (htarget p) (hdist p)
      (fun z hz v => hbounds p 0 H.time_bounds z ?_ v) hx hy
    exact Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz)
  · intro p
    apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρ / 4)).image_of_continuousOn
    apply (Φ p).contMDiffOn.continuousOn.mono
    rw [hsource p]
    exact Metric.closedBall_subset_ball (by linarith)
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hcover₀ hx)
    let q : S := ⟨p, Finset.mem_insert_of_mem hp⟩
    have hxtarget : x ∈ (Φ q).target := by
      rw [htarget q]
      exact hxp.trans_le (ENNReal.ofReal_le_ofReal (by linarith : ρ / 4 ≤ R))
    have hwsource : (Φ q).symm x ∈ Metric.ball 0 R := by
      rw [← hsource q]
      exact (Φ q).map_target hxtarget
    have heq : Φ q ((Φ q).symm x) = x := (Φ q).right_inv hxtarget
    refine mem_iUnion.mpr ⟨q, (Φ q).symm x, ?_, heq⟩
    have hnorm := hdist q ((Φ q).symm x) hwsource
    rw [heq] at hnorm
    have hsmall : ENNReal.ofReal ‖(Φ q).symm x‖ < ENNReal.ofReal (ρ / 4) := by
      rw [← hnorm]
      exact hxp
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (show ‖(Φ q).symm x‖ < ρ / 4 from
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsmall).le

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
