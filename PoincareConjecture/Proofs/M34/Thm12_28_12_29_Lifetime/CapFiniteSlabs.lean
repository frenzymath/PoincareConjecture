import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapWorldlineSurvival












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R

include P



theorem standardFlow_chapter11_finite_slabs (p : ℕ → (G).point)
    (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop)
    (H : StandardFlowNoncollapsingCertificate F) {r0 : ℝ}
    (hradius : r0 ≤ H.radius) (hrtime : r0 ^ 2 ≤ F.base.lifetime / 4) (T A : ℝ) :
    ∀ᶠ k : ℕ in atTop, Nonempty (M30FiniteHorizonSlab
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) k A T H.kappa r0) := by
  let S := fixedFlowBlowupSequence (G) p hpositive hdiverges
  have hscaled := partialFlow_chapter11_scaled_time_tendsto F.base P R p hdiverges
  have htimes := partialFlow_chapter11_times_tendsto F.base P R p hdiverges
  have htail : ∀ᶠ k : ℕ in atTop, F.base.lifetime / 2 < (p k).1 :=
    (tendsto_order.mp htimes).1 _ (by linarith [F.base.lifetime_pos])
  filter_upwards [htail, hscaled.eventually_ge_atTop (2 * T)] with k hk hscaledk
  have hQ : 0 < S.scale k := hpositive k
  have hclock (s : ℝ) (hs : s ∈ Ioc (-T) 0) :
      F.base.lifetime / 4 ≤ (p k).1 + s / S.scale k ∧
        (p k).1 + s / S.scale k < F.base.lifetime := by
    have hdiv : T / S.scale k ≤ (p k).1 / 2 := by
      apply (div_le_iff₀ hQ).mpr
      change 2 * T ≤ S.scale k * (p k).1 at hscaledk
      nlinarith
    have hsdiv : -(T / S.scale k) < s / S.scale k := by
      simpa only [neg_div] using div_lt_div_of_pos_right hs.1 hQ
    refine ⟨by linarith, ?_⟩
    exact (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le)).trans_lt
      (ordinaryChapter11Point_time_mem R (p k)).2
  have hdomain (s : ℝ) (hs : s ∈ Ioc (-T) 0) :
      (p k).1 + s / S.scale k ∈ (partialFlowSpacetimeInterval F.base).domain :=
    ⟨(by linarith [F.base.lifetime_pos] : 0 ≤ F.base.lifetime / 4).trans (hclock s hs).1,
      (hclock s hs).2⟩
  refine ⟨{
    embedding := ordinaryChapter11Cylinder R (p k) (S.scale k) hQ
      (Ioc (-T) 0) (S.baseBall k A) hdomain
    zero_identity := fun hzero x _ => ordinaryChapter11Cylinder_zero_identity R
      (p k) (S.scale k) hQ (Ioc (-T) 0) (S.baseBall k A) hdomain hzero x
    noncollapsed := ?_
  }⟩
  intro s hs x _
  apply standardFlow_chapter11_noncollapsed F P R H hradius
  exact hrtime.trans (hclock s hs).1

end PoincareConjecture.M34
