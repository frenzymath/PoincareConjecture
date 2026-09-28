import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapChapter11Geometry
import PoincareConjecture.Proofs.M10.ScalarBound

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F) (F := F.flow) R

include P

theorem partialFlow_chapter11_scalar_past_bound {b : ℝ} (hb : b ∈ Ico 0 F.lifetime) :
    ∃ B : ℝ, ∀ p : (G).point, p.1 ≤ b → (G).scalar p ≤ B := by
  obtain ⟨B, _, hbound⟩ := M10.exists_uniform_scalarCurvature_bound F.flow
    (I := Icc 0 b) ⟨fun t ht => partialFlow_complete F P.curvature
      ⟨ht.1, ht.2.trans_lt hb.2⟩, F.curvature_locally_bounded b hb.1 hb.2⟩
  refine ⟨B, ?_⟩
  intro p hp
  exact (ordinaryChapter11_scalar_eq (I := partialFlowSpacetimeInterval F) (F := F.flow)
    R (partialFlow_chapter11_calculus F P R) p).le.trans
    ((le_abs_self _).trans (hbound p.1
      ⟨(ordinaryChapter11Point_time_mem R p).1, hp⟩ (ordinaryChapter11Projection R p)))

theorem partialFlow_chapter11_times_tendsto (p : ℕ → (G).point)
    (hscalar : Tendsto (fun k => (G).scalar (p k)) atTop atTop) :
    Tendsto (fun k => (p k).1) atTop (𝓝 F.lifetime) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hneg : a < 0
    · exact Eventually.of_forall fun k =>
        hneg.trans_le (ordinaryChapter11Point_time_mem R (p k)).1
    · obtain ⟨B, hbound⟩ := partialFlow_chapter11_scalar_past_bound F P R
        ⟨le_of_not_gt hneg, ha⟩
      filter_upwards [hscalar.eventually_gt_atTop B] with k hk
      by_contra h
      exact (not_le_of_gt hk) (hbound (p k) (le_of_not_gt h))
  · intro b hb
    exact Eventually.of_forall fun k =>
      (ordinaryChapter11Point_time_mem R (p k)).2.trans hb

theorem partialFlow_chapter11_scaled_time_tendsto (p : ℕ → (G).point)
    (hscalar : Tendsto (fun k => (G).scalar (p k)) atTop atTop) :
    Tendsto (fun k => (G).scalar (p k) * (p k).1) atTop atTop :=
  Filter.Tendsto.atTop_mul_pos F.lifetime_pos hscalar
    (partialFlow_chapter11_times_tendsto F P R p hscalar)

end PoincareConjecture.M34
