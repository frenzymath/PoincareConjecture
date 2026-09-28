import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapFiniteSlabs
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPoint
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryBoxScalar

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R

include P

theorem standardFlow_chapter11_long_controls (E0 : StandardCapEstimate g0)
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop)
    (H : StandardFlowNoncollapsingCertificate F) {r0 epsilon C A : ℝ}
    (hr0 : 0 < r0) (hradius : r0 ≤ H.radius) (hrtime : r0 ^ 2 ≤ F.base.lifetime / 4)
    (hepsilon : 0 < epsilon) (hC : 0 < C) (hA : 0 < A)
    (hgood : ∀ k, ∀ q : (G).point, q.1 ≤ (p k).1 →
      4 * (G).scalar (p k) ≤ (G).scalar q → Chapter11GoodPoint (G) epsilon C A q) :
    Nonempty (M30LongBlowupControls (fixedFlowBlowupSequence (G) p hpositive hdiverges)
      epsilon C H.kappa r0 1 ⊤) := by
  let S := fixedFlowBlowupSequence (G) p hpositive hdiverges
  refine ⟨{
    epsilon_pos := hepsilon
    C_pos := hC
    kappa_pos := H.kappa_pos
    radius_pos := hr0
    branch := fun _ => partialFlow_chapter11_branch F.base P E0 R
    canonical := fun k => chapter11GoodPoint_earlier_canonical (p k) (hgood k)
    analytic_constant := A
    analytic_constant_pos := hA
    scalar_gradient_bound := ?_
    scalar_time_derivative_bound := ?_
    balls_compact := ?_
    noncollapsed_at_zero := ?_
    mu_pos := zero_lt_one
    maximal_worldlines := partialFlow_chapter11_worldline_survival F.base P R
      p hpositive hdiverges zero_le_one
    horizon_pos := by simp
    slabs := fun T _ _ B _ => standardFlow_chapter11_finite_slabs F P R
      p hpositive hdiverges H hradius hrtime T B
  }⟩
  · intro k t _ htime x hhigh
    exact (hgood k ⟨t, x⟩ htime hhigh).scalar_gradient
  · intro k b t ht htime x hhigh
    have he := ordinaryChapter11_box_scalar_eq (I := partialFlowSpacetimeInterval F.base)
      (F := F.base.flow) R (partialFlow_chapter11_calculus F.base P R) b ht x
    exact (hgood k ⟨t, ((G).box b).forward t ht x⟩ htime
      (hhigh.trans_eq he.symm)).scalar_time_derivative b ht x rfl
  · intro B _
    exact Eventually.of_forall fun k => partialFlow_chapter11_compact_ball F.base P R (p k)
      (B / Real.sqrt (S.scale k))
  · intro B _
    filter_upwards [standardFlow_chapter11_finite_slabs F P R p hpositive hdiverges
      H hradius hrtime 1 B] with k hk
    obtain ⟨slab⟩ := hk
    intro x hx
    have hzero : (0 : ℝ) ∈ Ioc (-1) 0 := by norm_num
    have h := slab.noncollapsed 0 hzero x hx
    rwa [slab.zero_identity hzero x hx] at h

end PoincareConjecture.M34
