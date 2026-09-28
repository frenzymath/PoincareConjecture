import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapLongControls
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapBadPoints

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R

include P

theorem standardFlow_chapter11_bad_limit (E0 : StandardCapEstimate g0)
    (H : StandardFlowNoncollapsingCertificate F) {epsilon0 epsilon C A : ℝ}
    (long : M30LongLimitStatement.{0} epsilon0) (hepsilon : 0 < epsilon)
    (hepsilon0 : epsilon ≤ epsilon0) (hC : 0 < C) (hA : 0 < A)
    (hbad : ∀ Q : ℝ, 0 < Q → ∃ p : (G).point, Q ≤ (G).scalar p ∧
      ¬ Chapter11GoodPoint (G) epsilon C A p) :
    ∃ (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
      (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) (r0 : ℝ),
      0 < r0 ∧ (∀ k, ¬ Chapter11GoodPoint (G) epsilon C A (p k)) ∧
      Nonempty (RepairedLongControlledBlowupConclusion
        (fixedFlowBlowupSequence (G) p hpositive hdiverges) H.kappa r0 ⊤) := by
  obtain ⟨p, hp, hdiverges⟩ := partialFlow_chapter11_bad_points F.base P R
    (Chapter11GoodPoint (G) epsilon C A) hbad
  have hpositive (k : ℕ) : 0 < (G).scalar (p k) :=
    lt_trans (by positivity) (hp k).1
  let r0 := min H.radius (Real.sqrt (F.base.lifetime / 4))
  have htail : 0 < F.base.lifetime / 4 := div_pos F.base.lifetime_pos (by norm_num)
  have hr0 : 0 < r0 := lt_min H.radius_pos (Real.sqrt_pos.mpr htail)
  have hradius : r0 ≤ H.radius := min_le_left _ _
  have hrtime : r0 ^ 2 ≤ F.base.lifetime / 4 := calc
    r0 ^ 2 ≤ (Real.sqrt (F.base.lifetime / 4)) ^ 2 :=
      pow_le_pow_left₀ hr0.le (min_le_right _ _) _
    _ = F.base.lifetime / 4 := Real.sq_sqrt htail.le
  obtain ⟨controls⟩ := standardFlow_chapter11_long_controls F P R E0
    p hpositive hdiverges H hr0 hradius hrtime hepsilon hC hA (fun k => (hp k).2.2)
  exact ⟨p, hpositive, hdiverges, r0, hr0, fun k => (hp k).2.1,
    long _ epsilon C H.kappa r0 1 ⊤ hepsilon0 controls⟩

end PoincareConjecture.M34
