import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Round.HornTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.PrefixInterior

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)

theorem isClosed_coordinateClosedTail (a : ℝ) :
    IsClosed (Subtype.val '' {x : horn.carrier | a ≤ horn.coordinateHeight x}) := by
  exact horn.isClosed_carrier.isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_le continuous_const horn.continuous_coordinateHeight)

theorem exists_positive_coordinate_lower_bound
    {K : Set (E.extended.slice T).carrier} (hK : IsCompact K) (hne : K.Nonempty)
    (hKH : K ⊆ horn.carrier \ horn.boundary_sphere) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      K ⊆ Subtype.val '' {x : horn.carrier | a ≤ horn.coordinateHeight x} := by
  let L : Set horn.carrier := Subtype.val ⁻¹' K
  have hL : IsCompact L := horn.isClosed_carrier.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hLne : L.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, (hKH hx).1⟩, hx⟩
  obtain ⟨x, hx, hmin⟩ := hL.exists_isMinOn hLne horn.continuous_coordinateHeight.continuousOn
  have hxpos : 0 < horn.coordinateHeight x := by
    apply lt_of_le_of_ne (horn.coordinate.symm x).2.property.1
    intro heq
    apply (hKH hx).2
    rw [horn.boundary_sphere_eq]
    refine ⟨((horn.coordinate.symm x).1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
    have hp := horn.parameterization_coordinate_symm x
    change horn.parameterization ((horn.coordinate.symm x).1,
      horn.coordinateHeight x) = x.val at hp
    change 0 = horn.coordinateHeight x at heq
    rwa [← heq] at hp
  refine ⟨horn.coordinateHeight x, hxpos, (horn.coordinate.symm x).2.property.2, ?_⟩
  intro y hy
  exact ⟨⟨y, (hKH hy).1⟩, hmin hy, rfl⟩

theorem isPreconnected_interior_diff_coordinateClosedTail {a : ℝ}
    (ha1 : a < 1) :
    IsPreconnected ((horn.carrier \ horn.boundary_sphere) \
      Subtype.val '' {x : horn.carrier | a ≤ horn.coordinateHeight x}) := by
  have heq : (horn.carrier \ horn.boundary_sphere) \
      Subtype.val '' {x : horn.carrier | a ≤ horn.coordinateHeight x} =
      horn.parameterization '' (univ ×ˢ Ioo (0 : ℝ) a) := by
    ext x
    constructor
    · rintro ⟨hxH, hxY⟩
      obtain ⟨⟨q, t⟩, ⟨_, ht0, ht1⟩, rfl⟩ :=
        horn.carrier_diff_boundary_eq_image ▸ hxH
      have hta : t < a := by
        by_contra h
        apply hxY
        refine ⟨horn.coordinate (q, ⟨t, ht0.le, ht1⟩), ?_, horn.coordinate_eq _⟩
        change a ≤ horn.coordinateHeight (horn.coordinate (q, ⟨t, ht0.le, ht1⟩))
        simpa only [coordinateHeight, Homeomorph.symm_apply_apply] using le_of_not_gt h
      exact ⟨(q, t), ⟨mem_univ _, ht0, hta⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht0, hta⟩, rfl⟩
      refine ⟨horn.carrier_diff_boundary_eq_image.symm ▸
        (show horn.parameterization (q, t) ∈
          horn.parameterization '' (univ ×ˢ Ioo (0 : ℝ) 1) from
          ⟨(q, t), ⟨mem_univ _, ht0, hta.trans ha1⟩, rfl⟩), ?_⟩
      rintro ⟨x, hx, heq⟩
      have hcoord : x = horn.coordinate (q, ⟨t, ht0.le, hta.trans ha1⟩) :=
        Subtype.ext (heq.trans (horn.coordinate_eq (q, ⟨t, ht0.le, hta.trans ha1⟩)).symm)
      rw [hcoord] at hx
      have hle : a ≤ t := by simpa [coordinateHeight] using hx
      exact (not_le_of_gt hta) hle
  rw [heq]
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  apply (isPreconnected_univ.prod isPreconnected_Ioo).image
  apply horn.parameterization_smooth.continuousOn.mono
  exact fun _ hz => ⟨mem_univ _, (neg_lt_zero.mpr horn.collar_pos).trans hz.2.1,
    hz.2.2.trans ha1⟩

theorem contained_neck_isSeparating {delta : ℝ} (N : TerminalStrongNeck E delta)
    (hdelta : delta < 1 / 2) (hN : N.carrier ⊆ horn.carrier) :
    (N.spatialNeck hdelta).IsSeparating := by
  have hNi : N.carrier ⊆ horn.carrier \ horn.boundary_sphere := by
    intro x hx
    refine ⟨hN hx, ?_⟩
    exact fun hb => horn.boundary_sphere_not_mem_interior hb
      (N.carrier_open.subset_interior_iff.mpr hN hx)
  obtain ⟨a, ha0, ha1, hSa⟩ := horn.exists_positive_coordinate_lower_bound
    N.isCompact_central_sphere ⟨N.center, N.center_on_central_sphere⟩
      (N.central_sphere_subset.trans hNi)
  let Y := Subtype.val '' {x : horn.carrier | a ≤ horn.coordinateHeight x}
  have hYU : Y ⊆ horn.interiorOpens := by
    rintro x ⟨y, hy, rfl⟩
    rw [show (horn.interiorOpens : Set _) = horn.carrier \ horn.boundary_sphere from rfl,
      horn.carrier_diff_boundary_eq_image]
    exact ⟨((horn.coordinate.symm y).1, (horn.coordinate.symm y).2),
      ⟨mem_univ _, ha0.trans_le hy, (horn.coordinate.symm y).2.property.2⟩,
      horn.parameterization_coordinate_symm y⟩
  let : SimplyConnectedSpace horn.interiorOpens := horn.simplyConnectedSpace_interior
  exact (N.spatialNeck hdelta).isSeparating_of_closed_subset_of_simplyConnected_open
    horn.interiorOpens (horn.isClosed_coordinateClosedTail a) hYU
      (horn.isPreconnected_interior_diff_coordinateClosedTail ha1) hNi hSa

end PoincareConjecture.StrongHorn
