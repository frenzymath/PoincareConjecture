import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Buffered.Paths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Intrinsic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)
  (N : EpsilonNeck (K.flow.metric 0))

theorem buffered_intrinsic_neck_distance_lt
    (heps : N.epsilon = epsilon) (hscale : N.scale = G.neck.terminal_neck.scale)
    {a b : ℝ} {x y : M} (hx : x ∈ N.region a b) (hy : y ∈ N.region a b) :
    intrinsicEDist (K.flow.metric 0) (N.region a b) x y <
      ENNReal.ofReal (R * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  have hepsilon : 0 < epsilon := heps ▸ N.epsilon_pos
  have hroot : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  have hroot₂ : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have haxis : |(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| ≤
      2 * epsilon⁻¹ := by
    have hx' := (N.coordinate_inverse_mem x hx.1).2
    have hy' := (N.coordinate_inverse_mem y hy.1).2
    rw [heps] at hx' hy'
    apply abs_le.mpr
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have hbound : N.scale * Real.sqrt (1 + N.epsilon) *
      (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
        Real.sqrt 2 * (Real.pi + 1)) ≤
      (8 * Real.pi + 4 * epsilon⁻¹ + 4) * N.scale := by
    calc
      _ ≤ N.scale * 2 * (2 * epsilon⁻¹ + 2 * (Real.pi + 1)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hroot N.scale_pos.le
        · exact add_le_add haxis (mul_le_mul_of_nonneg_right hroot₂ (by positivity))
        · positivity
        · exact mul_nonneg N.scale_pos.le (by norm_num)
      _ ≤ (8 * Real.pi + 4 * epsilon⁻¹ + 4) * N.scale := by
        nlinarith [mul_pos Real.pi_pos N.scale_pos]
  have hsmall : (8 * Real.pi + 4 * epsilon⁻¹ + 4) * N.scale <
      R * soulScalar K S.center ^ (-1 / 2 : ℝ) := hscale.symm ▸ G.neck_scale_bound
  exact (N.intrinsicEDist_region_le_axial_add hx hy).trans_lt
    (ENNReal.ofReal_lt_ofReal_iff G.radius_scale_pos |>.mpr (hbound.trans_lt hsmall))

theorem central_sphere_subset_buffered_region
    (hsphere : N.central_sphere = G.neck.terminal_neck.central_sphere)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    G.neck.terminal_neck.central_sphere ⊆ N.region a b := by
  intro x hx
  have h := (N.mem_central_sphere_iff x).mp (hsphere.symm ▸ hx)
  exact ⟨h.1, h.2.symm ▸ ha, h.2.symm ▸ hb⟩

theorem buffered_exists_intrinsic_path_to_boundary
    (hsphere : N.central_sphere = G.neck.terminal_neck.central_sphere)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) {x : M} (hx : x ∈ G.inside) :
    ∃ y ∈ G.neck.terminal_neck.central_sphere,
      intrinsicEDist (K.flow.metric 0) (G.inside ∪ N.region a b) x y ≤
        (K.flow.metric 0).edist x y ∧
      ((K.flow.metric 0).edist x y).toReal ≤
        ((K.flow.metric 0).edist x G.neck.terminal_neck.center).toReal := by
  have hfront : (frontier (closure G.inside)).Nonempty :=
    G.frontier_closure_inside ▸
      ⟨G.neck.terminal_neck.center, G.neck.terminal_neck.center_on_central_sphere⟩
  obtain ⟨y, hy, hL, hnear, γ, hγ0, hγL, hgeo, hspeed, _, hinside⟩ :=
    (K.flow.metric 0).exists_unit_speed_minimizing_geodesic_to_frontier
      (K.complete 0 le_rfl) G.compact_side hfront (G.interior_closure_inside.symm ▸ hx)
  have hysphere := G.frontier_closure_inside ▸ hy
  refine ⟨y, hysphere, ?_, hnear G.neck.terminal_neck.center
    (G.frontier_closure_inside ▸ G.neck.terminal_neck.center_on_central_sphere)⟩
  have hmap : MapsTo γ (Icc 0 ((K.flow.metric 0).edist x y).toReal)
      (G.inside ∪ N.region a b) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact Or.inl (G.interior_closure_inside ▸ hinside ⟨ht.1, hlt⟩)
    · rw [heq, hγL]
      exact Or.inr (G.central_sphere_subset_buffered_region N hsphere ha hb hysphere)
  have hpath := intrinsicEDist_le_pathELength_on (K.flow.metric 0) hL
    (hgeo.contMDiffOn.of_le (by simp)) hγ0 hγL hmap
  apply hpath.trans_eq
  rw [(K.flow.metric 0).pathELength_eq_of_tangentNorm_eq hspeed]
  simp only [ENNReal.ofReal_one, sub_zero, one_mul,
    ENNReal.ofReal_toReal ((K.flow.metric 0).edist_ne_top x y)]

theorem buffered_intrinsic_distance_to_center_lt
    (heps : N.epsilon = epsilon) (hscale : N.scale = G.neck.terminal_neck.scale)
    (hsphere : N.central_sphere = G.neck.terminal_neck.central_sphere)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {x : M} (hx : x ∈ G.inside ∪ N.region a b) :
    intrinsicEDist (K.flow.metric 0) (G.inside ∪ N.region a b)
      x G.neck.terminal_neck.center <
        ENNReal.ofReal ((4 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  have hcenter := G.central_sphere_subset_buffered_region N hsphere ha hb
    G.neck.terminal_neck.center_on_central_sphere
  have hneck {y : M} (hy : y ∈ N.region a b) :
      intrinsicEDist (K.flow.metric 0) (G.inside ∪ N.region a b)
        y G.neck.terminal_neck.center <
      ENNReal.ofReal (R * soulScalar K S.center ^ (-1 / 2 : ℝ)) :=
    (intrinsicEDist_mono (K.flow.metric 0) subset_union_right).trans_lt
      (G.buffered_intrinsic_neck_distance_lt N heps hscale hy hcenter)
  rcases hx with hx | hx
  · obtain ⟨y, hy, hpath, hnear⟩ :=
      G.buffered_exists_intrinsic_path_to_boundary N hsphere ha hb hx
    have hxball := (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top S.center x)).mp (G.carrier_subset_ball (Or.inl hx))
    have htriangle := (K.flow.metric 0).toReal_edist_triangle x S.center G.neck.terminal_neck.center
    have hcenter' : ((K.flow.metric 0).edist S.center G.neck.terminal_neck.center).toReal =
        R * soulScalar K S.center ^ (-1 / 2 : ℝ) := G.neck.terminal_center ▸ G.center_radius
    rw [hcenter'] at htriangle
    have hcomm : (K.flow.metric 0).edist x S.center = (K.flow.metric 0).edist S.center x := by
      let := (K.flow.metric 0).toMetricSpace
      exact edist_comm x S.center
    rw [hcomm] at htriangle
    have hdist : (K.flow.metric 0).edist x y <
        ENNReal.ofReal ((3 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) :=
      (ENNReal.lt_ofReal_iff_toReal_lt ((K.flow.metric 0).edist_ne_top x y)).mpr (by nlinarith)
    have hsum := ENNReal.add_lt_add (hpath.trans_lt hdist)
      (hneck (G.central_sphere_subset_buffered_region N hsphere ha hb hy))
    apply (intrinsicEDist_triangle (K.flow.metric 0)).trans_lt
    convert hsum using 1
    rw [← ENNReal.ofReal_add (by nlinarith [G.radius_scale_pos]) G.radius_scale_pos.le]
    congr 1
    ring
  · apply (hneck hx).trans_le
    apply ENNReal.ofReal_le_ofReal
    nlinarith [G.radius_scale_pos]

theorem buffered_intrinsic_diameter_bound
    (heps : N.epsilon = epsilon) (hscale : N.scale = G.neck.terminal_neck.scale)
    (hsphere : N.central_sphere = G.neck.terminal_neck.central_sphere)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    intrinsicDiameter (K.flow.metric 0) (G.inside ∪ N.region a b) <
      ENNReal.ofReal ((9 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  have hdiam : intrinsicDiameter (K.flow.metric 0) (G.inside ∪ N.region a b) ≤
      ENNReal.ofReal ((8 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
    apply sSup_le
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have hx := G.buffered_intrinsic_distance_to_center_lt N heps hscale hsphere ha hb x.property
    have hy := G.buffered_intrinsic_distance_to_center_lt N heps hscale hsphere ha hb y.property
    rw [intrinsicEDist_comm] at hy
    apply (intrinsicEDist_triangle (K.flow.metric 0)).trans
    have hsum := add_le_add hx.le hy.le
    convert hsum using 1
    rw [← ENNReal.ofReal_add (by nlinarith [G.radius_scale_pos])
      (by nlinarith [G.radius_scale_pos])]
    congr 1
    ring
  apply hdiam.trans_lt
  apply ENNReal.ofReal_lt_ofReal_iff (by nlinarith [G.radius_scale_pos]) |>.mpr
  nlinarith [G.radius_scale_pos]

end PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion
