import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
# The actual full regular-limit identification

If an event's regular-limit domain is the entire pre-carrier, its retained
limit maps are a global smooth diffeomorphism. This is the map used when
testing the full-limit case against maximality, not a newly selected map.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- The actual regular-limit maps, when their domain is all of the pre-slice. -/
def limitDiffeomorph (E : SurgeryEventData g₀ K P slice metric T)
    (hfull : E.regular_limit = Set.univ) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice E.tMinus).carrier E.terminal.carrier ∞ where
  toFun := E.limit_identify.map
  invFun := E.limit_identify.inverse
  left_inv x := E.limit_identify.left_inverse (by rw [hfull]; trivial)
  right_inv x := E.limit_identify.right_inverse (Set.mem_univ x)
  contMDiff_toFun := by
    apply contMDiffOn_univ.mp
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.limit_identify.map Set.univ
    rw [← hfull]
    exact E.limit_identify.map_smooth
  contMDiff_invFun := contMDiffOn_univ.mp E.limit_identify.inverse_smooth

@[simp] theorem limitDiffeomorph_apply
    (E : SurgeryEventData g₀ K P slice metric T)
    (hfull : E.regular_limit = Set.univ) (x : (slice E.tMinus).carrier) :
    E.limitDiffeomorph hfull x = E.limit_identify.map x := rfl

@[simp] theorem limitDiffeomorph_symm_apply
    (E : SurgeryEventData g₀ K P slice metric T)
    (hfull : E.regular_limit = Set.univ) (x : E.terminal.carrier) :
    (E.limitDiffeomorph hfull).symm x = E.limit_identify.inverse x := rfl

end PoincareMT.SurgeryEventData
