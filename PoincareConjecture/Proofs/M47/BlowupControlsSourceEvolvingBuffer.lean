import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

theorem exists_standard_evolving_neck_initial_buffer
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma epsilon : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z (Ioc (-(1 + gamma)) 0))
    (hge : gamma < epsilon) (hepsilon : epsilon < 1 / 2) :
    ∃ A : ℝ, 0 < A ∧ ∃ E : EpsilonNeck (G.metric v),
      E.epsilon = epsilon ∧ E.connection = G.connection v ∧ E.center = z ∧
      E.coordinate_map = N.patch.coordinate ∧
      E.carrier ⊆ g0.metric.ball 0 A := by
  obtain ⟨E, he, hD, hcenter, hmap, _hinverse⟩ :=
    exists_standard_evolving_neck_spatial_restriction N hge.le hepsilon
  have hzero : (0 : ℝ) ∈ Ioc (-(1 + gamma)) 0 := by
    constructor <;> linarith only [N.epsilon_pos]
  let K := (N.staticAtZero hzero).toEpsilonNeck
  have hwidth : epsilon⁻¹ < K.epsilon⁻¹ :=
    (inv_lt_inv₀ (N.epsilon_pos.trans hge) N.epsilon_pos).mpr hge
  have hcompact : IsCompact (K.coordinate_map '' (univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹)) :=
    K.isCompact_image_closed_axial_interval (neg_lt_neg hwidth) hwidth
  obtain ⟨r, hr, hbuffer⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : StandardCapSpace)
  have hA : 0 < M36.radialArclength g0 r := by
    simpa only [M36.radialArclength_zero] using (M36.radialArclength_strictMono g0) hr
  refine ⟨M36.radialArclength g0 r, hA, E, he, hD, hcenter, hmap, ?_⟩
  intro x hx
  rw [M36.standard_ball_eq_euclidean g0 hA, M36.radialEuclideanRadius_arclength]
  apply hbuffer
  refine ⟨E.coordinate_inverse x, ?_, ?_⟩
  · have haxis := E.coordinate_inverse_mem x hx
    rw [he] at haxis
    exact ⟨mem_univ _, haxis.2.1.le, haxis.2.2.le⟩
  · change N.patch.coordinate (E.coordinate_inverse x) = x
    rw [← hmap]
    exact E.coordinate_map_coordinate_inverse hx

end PoincareConjecture.M47
