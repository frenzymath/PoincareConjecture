import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Paths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Boundary

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

include G

theorem radius_scale_pos : 0 < R * soulScalar K S.center ^ (-1 / 2 : ℝ) := by
  have hepsilon : 0 < epsilon := G.neck.terminal_epsilon ▸ G.neck.terminal_neck.epsilon_pos
  have hscale := G.neck.terminal_neck.scale_pos
  exact (by positivity : 0 < (8 * Real.pi + 4 * epsilon⁻¹ + 4) *
    G.neck.terminal_neck.scale).trans G.neck_scale_bound

theorem intrinsic_neck_distance_lt {x y : M}
    (hx : x ∈ G.neck.terminal_neck.carrier) (hy : y ∈ G.neck.terminal_neck.carrier) :
    intrinsicEDist (K.flow.metric 0) G.neck.terminal_neck.carrier x y <
      ENNReal.ofReal (R * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  let N := G.neck.terminal_neck
  have hepsilon : 0 < epsilon := G.neck.terminal_epsilon ▸ G.neck.terminal_neck.epsilon_pos
  have hscale := N.scale_pos
  have heps : N.epsilon = epsilon := G.neck.terminal_epsilon
  have hroot : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  have hroot₂ : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have haxis : |(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| ≤
      2 * epsilon⁻¹ := by
    have hx' := (N.coordinate_inverse_mem x hx).2
    have hy' := (N.coordinate_inverse_mem y hy).2
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
        · exact mul_le_mul_of_nonneg_left hroot hscale.le
        · exact add_le_add haxis (mul_le_mul_of_nonneg_right hroot₂ (by positivity))
        · positivity
        · positivity
      _ ≤ (8 * Real.pi + 4 * epsilon⁻¹ + 4) * N.scale := by
        nlinarith [mul_pos Real.pi_pos hscale]
  exact (N.intrinsicEDist_le_axial_add hx hy).trans_lt
    (ENNReal.ofReal_lt_ofReal_iff G.radius_scale_pos |>.mpr
      (hbound.trans_lt G.neck_scale_bound))

theorem closure_inside_subset_carrier :
    closure G.inside ⊆ G.inside ∪ G.neck.terminal_neck.carrier := by
  intro x hx
  by_cases hxA : x ∈ G.inside
  · exact Or.inl hxA
  · exact Or.inr (G.neck.terminal_neck.central_sphere_subset
      (G.inside_frontier ▸ ⟨hx, fun hi => hxA (interior_subset hi)⟩))

theorem exists_intrinsic_path_to_boundary {x : M} (hx : x ∈ G.inside) :
    ∃ y ∈ G.neck.terminal_neck.central_sphere,
      intrinsicEDist (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) x y ≤
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
      (G.inside ∪ G.neck.terminal_neck.carrier) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact Or.inl (G.interior_closure_inside ▸ hinside ⟨ht.1, hlt⟩)
    · rw [heq, hγL]
      exact Or.inr (G.neck.terminal_neck.central_sphere_subset hysphere)
  have hpath := intrinsicEDist_le_pathELength_on (K.flow.metric 0) hL
    (hgeo.contMDiffOn.of_le (by simp)) hγ0 hγL hmap
  apply hpath.trans_eq
  rw [(K.flow.metric 0).pathELength_eq_of_tangentNorm_eq hspeed]
  simp only [ENNReal.ofReal_one, sub_zero, one_mul,
    ENNReal.ofReal_toReal ((K.flow.metric 0).edist_ne_top x y)]

theorem intrinsic_distance_to_center_lt {x : M}
    (hx : x ∈ G.inside ∪ G.neck.terminal_neck.carrier) :
    intrinsicEDist (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier)
      x G.neck.terminal_neck.center <
        ENNReal.ofReal ((4 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  have hcenter := G.neck.terminal_neck.central_sphere_subset
    G.neck.terminal_neck.center_on_central_sphere
  have hneck {y : M} (hy : y ∈ G.neck.terminal_neck.carrier) :
      intrinsicEDist (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier)
        y G.neck.terminal_neck.center <
      ENNReal.ofReal (R * soulScalar K S.center ^ (-1 / 2 : ℝ)) :=
    (intrinsicEDist_mono (K.flow.metric 0) subset_union_right).trans_lt
      (G.intrinsic_neck_distance_lt hy hcenter)
  rcases hx with hx | hx
  · obtain ⟨y, hy, hpath, hnear⟩ := G.exists_intrinsic_path_to_boundary hx
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
      (hneck (G.neck.terminal_neck.central_sphere_subset hy))
    apply (intrinsicEDist_triangle (K.flow.metric 0)).trans_lt
    convert hsum using 1
    rw [← ENNReal.ofReal_add (by nlinarith [G.radius_scale_pos]) G.radius_scale_pos.le]
    congr 1
    ring
  · apply (hneck hx).trans_le
    apply ENNReal.ofReal_le_ofReal
    nlinarith [G.radius_scale_pos]

theorem intrinsic_diameter_bound :
    intrinsicDiameter (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
      ENNReal.ofReal ((9 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  have hdiam : intrinsicDiameter (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) ≤
      ENNReal.ofReal ((8 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
    apply sSup_le
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have hx := G.intrinsic_distance_to_center_lt x.property
    have hy := G.intrinsic_distance_to_center_lt y.property
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
