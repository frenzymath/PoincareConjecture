import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GeneralizedStrongNeck

theorem isPreconnected_carrier {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) : IsPreconnected N.carrier := by
  let : PreconnectedSpace (Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  have heq : Set.range (fun z : NeckDomain epsilon => (N.coordinate z).val) = N.carrier := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (N.coordinate z).property
    · intro hx
      obtain ⟨z, hz⟩ := N.coordinate.surjective ⟨x, hx⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  rw [← heq]
  exact isPreconnected_range (continuous_subtype_val.comp N.coordinate.continuous)

theorem exists_scalar_control :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
        (N : GeneralizedStrongNeck F t epsilon), epsilon ≤ epsilon₀ →
        ∀ x ∈ N.carrier,
          (F.connection t).scalarCurvature N.center / 2 <
            (F.connection t).scalarCurvature x ∧
          (F.connection t).scalarCurvature x <
            2 * (F.connection t).scalarCurvature N.center := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F t epsilon N he x hx
  have hehalf : epsilon < 1 / 2 := lt_of_le_of_lt (he.trans hsmall) (by norm_num)
  let S := N.spatialNeck hehalf
  obtain ⟨z, hz⟩ := N.coordinate.surjective ⟨x, hx⟩
  have hxmap : N.coordinate_map (z.1, (z.2 : ℝ)) = x :=
    (N.coordinate_map_eq z).symm.trans (congrArg Subtype.val hz)
  have hbound := (hcontrol S (F.connection t) he z.1 z.2.property).1
  change |N.scale ^ 2 * (F.connection t).scalarCurvature
    (N.coordinate_map (z.1, (z.2 : ℝ))) - 1| < 1 / 2 at hbound
  rw [hxmap] at hbound
  have hnormal : N.scale ^ 2 * (F.connection t).scalarCurvature N.center = 1 :=
    S.scale_sq_mul_scalar_center
  have hs : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
  constructor
  · apply (mul_lt_mul_iff_right₀ hs).mp
    nlinarith only [hnormal, (abs_lt.mp hbound).1]
  · apply (mul_lt_mul_iff_right₀ hs).mp
    nlinarith only [hnormal, (abs_lt.mp hbound).2]

end PoincareConjecture.GeneralizedStrongNeck
