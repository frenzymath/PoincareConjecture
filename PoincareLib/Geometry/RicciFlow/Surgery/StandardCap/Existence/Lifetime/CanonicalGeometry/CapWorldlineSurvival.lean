import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Flow.FixedFlowSequence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Curvature.CapScalarBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryMaximalLine

/-!
# Maximal worldline survival for a cap blow-up sequence

The requested normalized duration is at most mu, since its denominator
is at least the positive blow-up scale. Divergence of scale times base
time places the whole requested closed interval in the actual lifetime.
Source: Morgan-Tian Theorems 11.1 and 12.28, pp. 269-271, 323-324;
bad-point selection derivation, section 7.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M34

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F) (F := F.flow) R

include P

/-- Every cap scalar blow-up sequence has actual maximal worldlines with
the curvature-dependent normalized backward duration (Theorem 12.28). -/
theorem partialFlow_chapter11_worldline_survival (p : ℕ → (G).point)
    (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop)
    {mu : ℝ} (hmu : 0 ≤ mu) :
    GeneralizedMaximalBackwardFlowLineSurvival
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) mu := by
  let S := fixedFlowBlowupSequence (G) p hpositive hdiverges
  have htime := partialFlow_chapter11_scaled_time_tendsto F P R p hdiverges
  intro _ _
  filter_upwards [htime.eventually_ge_atTop mu] with k hk
  intro x _
  let d := m30BackwardDuration S k x mu
  have hQ : 0 < S.scale k := hpositive k
  have hm : 0 < max (S.scale k) ((G).scalar ⟨(p k).1, x⟩) :=
    hQ.trans_le (le_max_left _ _)
  have hd : d ≤ mu := by
    apply (div_le_iff₀ hm).mpr
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hmu
  refine ⟨ordinaryChapter11MaximalLine (I := partialFlowSpacetimeInterval F) (F := F.flow)
    R ⟨(p k).1, x⟩ (S.scale k) d hQ ?_⟩
  intro s hs
  have hclock : (p k).1 ∈ Ico 0 F.lifetime := ordinaryChapter11Point_time_mem R (p k)
  constructor
  · have hlow : -(p k).1 ≤ s / S.scale k := by
      apply (le_div_iff₀ hQ).mpr
      change mu ≤ S.scale k * (p k).1 at hk
      nlinarith [hs.1]
    linarith
  · exact (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le)).trans_lt hclock.2

end PoincareMT.M34
