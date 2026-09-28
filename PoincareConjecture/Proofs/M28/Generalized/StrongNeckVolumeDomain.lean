import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeCharts
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open tube

private abbrev E := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem normalized_neck_height_lt_of_mem_ball (N : EpsilonNeck g)
    (hscale : N.scale = 1) (hcarrier : N.carrier = univ)
    {S : ℝ} (hS : 0 < S) {x : M} (hx : x ∈ g.ball N.center S) :
    |(N.coordinate_inverse x).2| < 2 * S := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hx
  have hγN : MapsTo γ (Icc (0 : ℝ) 1) N.carrier := by
    rw [hcarrier]
    exact mapsTo_univ _ _
  have hcenter : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier
      (N.central_sphere_subset N.center_on_central_sphere)).mp
        N.center_on_central_sphere
  have hbound := path_axial_displacement_le N zero_le_one hγ hγN
  rw [h0, h1, hscale, hcenter, sub_zero] at hbound
  have hreal : (1 / 2 : ℝ) * |(N.coordinate_inverse x).2| < S :=
    (ENNReal.ofReal_lt_ofReal_iff hS).mp (hbound.trans_lt hlength)
  linarith

theorem normalized_neck_unit_ball_subset_domain (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ (1 / 200 : ℝ)) {S : ℝ}
    (hS : S ≤ N.epsilon⁻¹ / 16) (q : UnitTwoSphere) {s : ℝ}
    (hs : |s| ≤ 2 * S) :
    Metric.closedBall (0 : E) 1 ⊆ cylinderNeckChartDomain N q s := by
  have hinv : (200 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := one_div_le_one_div_of_le N.epsilon_pos hsmall
    norm_num at h
    exact h
  intro x hx
  have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hlast : |x (2 : Fin 3)| ≤ 1 := by
    apply le_trans _ hxnorm
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (2 : Fin 3)
  have hsource : x ∈ (neckVolumeModelChart q s).source := by
    rw [neckVolumeModelChart_source]
    exact mem_univ _
  change x ∈ (univ : Set E) ∧
    (cylinderScalarCoordinates s x).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ∧
    (cylinderScalarCoordinates s x).2 ∈ (univ : Set ℝ) at hsource
  change (cylinderScalarCoordinates s x).1 ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ∧
    -N.epsilon⁻¹ < (cylinderScalarCoordinates s x).2 ∧
    (cylinderScalarCoordinates s x).2 < N.epsilon⁻¹
  refine ⟨hsource.2.1, ?_, ?_⟩
  · change -N.epsilon⁻¹ < x (2 : Fin 3) + s
    linarith [(abs_le.mp hs).1, (abs_le.mp hlast).1]
  · change x (2 : Fin 3) + s < N.epsilon⁻¹
    linarith [(abs_le.mp hs).2, (abs_le.mp hlast).2]

theorem normalized_neck_isCompact_center_ball [T2Space M]
    (N : EpsilonNeck g) (hscale : N.scale = 1) {S : ℝ}
    (hS : S ≤ N.epsilon⁻¹ / 16) :
    IsCompact (closure (g.ball N.center S)) := by
  have hcompact :=
    (N.precompact_ball_of_central_sphere N.center_on_central_sphere).1
  rw [hscale, one_mul] at hcompact
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  apply hx.trans_le (ENNReal.ofReal_le_ofReal ?_)
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  linarith

end PoincareConjecture.M28
