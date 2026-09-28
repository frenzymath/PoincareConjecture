import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPointAnalyticAncient
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPointAnalyticLimits
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapBadLimit












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M34

section Threshold

variable {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R

include P

private theorem threshold_of_eventually_good (E0 : StandardCapEstimate g0)
    (H : StandardFlowNoncollapsingCertificate F) {epsilon0 epsilon c A : ℝ}
    (long : M30LongLimitStatement.{0} epsilon0) (hepsilon : 0 < epsilon)
    (hepsilon0 : epsilon ≤ epsilon0) (hc : 0 < c) (hA : 0 < A)
    (hgood : ∀ (p : ℕ → (G).point) (hp : ∀ k, 0 < (G).scalar (p k))
      (hd : Tendsto (fun k => (G).scalar (p k)) atTop atTop)
      (C : GeneralizedBlowupConvergence
        (fixedFlowBlowupSequence (G) p hp hd) (blowupBackwardInterval ⊤))
      (_K : M30AncientKappaIdentification C.limit H.kappa),
      ∀ᶠ k : ℕ in atTop, Chapter11GoodPoint (G) epsilon c A (p (C.subsequence k))) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ p : (G).point,
      Q ≤ (G).scalar p → Chapter11GoodPoint (G) epsilon c A p := by
  by_contra h
  push Not at h
  obtain ⟨p, hp, hd, r0, _, hbad, ⟨D⟩⟩ := standardFlow_chapter11_bad_limit F P R E0 H
    long hepsilon hepsilon0 hc hA h
  obtain ⟨K⟩ := D.ancient rfl
  obtain ⟨k, hk⟩ := (hgood p hp hd D.convergence K).exists
  exact hbad (D.convergence.subsequence k) hk

end Threshold




theorem standardFlow_chapter11_goodPoint_threshold_of_persistence
    (P : M34StandardCapPredecessors) :
    ∃ A : ℝ, 0 < A ∧ ∀ {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
      (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))
      (_E0 : StandardCapEstimate g0) (H : StandardFlowNoncollapsingCertificate F)
      {epsilon0 epsilon c : ℝ},
      let G := ordinaryChapter11Flow
        (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R
      M30LongLimitStatement.{0} epsilon0 → 0 < epsilon → epsilon ≤ epsilon0 → 0 < c →
      (∀ (p : ℕ → G.point) (hp : ∀ k, 0 < G.scalar (p k))
        (hd : Tendsto (fun k => G.scalar (p k)) atTop atTop)
        (C : GeneralizedBlowupConvergence
          (fixedFlowBlowupSequence G p hp hd) (blowupBackwardInterval ⊤))
        (_K : M30AncientKappaIdentification C.limit H.kappa),
        ∀ᶠ k : ℕ in atTop, Nonempty (GeneralizedCanonicalControl (F := G)
          (p (C.subsequence k)).1 (p (C.subsequence k)).2 epsilon c)) →
      ∃ Q : ℝ, 0 < Q ∧ ∀ p : G.point, Q ≤ G.scalar p → Chapter11GoodPoint G epsilon c A p := by
  obtain ⟨A, hA, hbound⟩ := exists_chapter11_analytic_constant P.kappa_alternatives
  refine ⟨A, hA, ?_⟩
  intro g0 F R E0 H epsilon0 epsilon c G long hepsilon hepsilon0 hc hcanonical
  apply threshold_of_eventually_good F P R E0 H long hepsilon hepsilon0 hc hA
  intro p hp hd C K
  have hJ : UniqueDiffOn ℝ (blowupBackwardInterval ⊤) := by
    rw [K.domain_eq]
    exact uniqueDiffOn_Iic 0
  have hlimits := hbound C.limit K
  exact ordinaryChapter11_eventually_goodPoint
    (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R p hp hd C hJ
    hlimits.1 hlimits.2 (hcanonical p hp hd C K)

end PoincareConjecture.M34
