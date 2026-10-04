import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.ShortTimeExistence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.FiniteLifetime
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.BoundedMaximality

/-!
# Actual maximal standard-cap existence

Short-time construction gives a first partial flow. Positive scalar
comparison bounds all partial lifetimes, and compatible chain unions
then give a maximal flow in the exact frozen sense. Each included metric
is complete (Morgan-Tian Definition 12.4 and Theorem 12.5, pp. 295-297).
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M34

/-- Every supplied standard initial metric admits an actual maximal cap
flow with complete slices (Theorem 12.5, pp. 295-297). -/
theorem maximalStandardCapFlow_exists (P : M34StandardCapPredecessors)
    (g0 : StandardInitialMetric) :
    ∃ F : MaximalStandardCapFlow g0,
      ∀ t ∈ Ico 0 F.base.lifetime, MetricComplete (F.metric t) := by
  obtain ⟨E0⟩ := standardCapEstimate_exists g0
  obtain ⟨F0, _hcomplete, _hbound⟩ := completePartialStandardCapFlow_exists P g0
  obtain ⟨F⟩ := maximalStandardCapFlow_exists_of_bounded_lifetimes F0
    (partialFlow_lifetime_le_scalar_bound P.curvature E0)
  exact ⟨F, fun _ ht => partialFlow_complete F.base P.curvature ht⟩

end PoincareMT.M34
