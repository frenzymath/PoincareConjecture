import PoincareConjecture.Proofs.M35.CapGeometry.LimitCapCanonical
import PoincareConjecture.Proofs.M35.CapGeometry.LimitFullStrongNeck
import PoincareConjecture.Proofs.M35.Thm12_28.LimitAlternatives
import PoincareConjecture.Proofs.M35.Thm12_28.AncientExtraction










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem exists_unit_time_canonical_constants (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀),
      ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
        ∀ t, ∀ ht : t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
          H ≤ (E.flow.connection t).scalarCurvature x →
          GeneralizedCanonicalControl (F := generalizedFlow E.flow.base.flow)
            t ((sliceDiffeomorph ht).symm x) epsilon C := by
  classical
  obtain ⟨deltaC, hdeltaC, hcap⟩ := blowupSequence_limit_cap_canonical P
  obtain ⟨deltaA, hdeltaA, hextract⟩ := exists_ancient_extraction_threshold P
  obtain ⟨deltaK, hdeltaK, hmodels⟩ := exists_limit_cap_or_neck_constants P
  refine ⟨min deltaC (min deltaA (min deltaK (1 / 24))),
    lt_min hdeltaC (lt_min hdeltaA (lt_min hdeltaK (by norm_num))), ?_⟩
  intro epsilon he hfine g₀ E
  have heC := hfine.trans (min_le_left _ _)
  have heA := hfine.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heK := hfine.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have he24 : epsilon ≤ 1 / 24 := hfine.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨NC⟩ := E.noncollapsing
  obtain ⟨C₀, hC₀, hcanonical⟩ := hmodels epsilon he heK
  let C := 8 * C₀ + 16 / NC.kappa
  have hC : 0 < C := add_pos (mul_pos (by norm_num) hC₀)
    (div_pos (by norm_num) NC.kappa_pos)
  suffices ∃ H : ℝ, 0 < H ∧
      ∀ t, ∀ ht : t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
        H ≤ (E.flow.connection t).scalarCurvature x →
        GeneralizedCanonicalControl (F := generalizedFlow E.flow.base.flow)
          t ((sliceDiffeomorph ht).symm x) epsilon C by
    obtain ⟨H, hH, hgood⟩ := this
    exact ⟨C, H, hC, hH, hgood⟩
  by_contra hnone
  push Not at hnone
  obtain ⟨t, x, ht, hR, _hhigh, hbad, hprior⟩ :=
    exists_strong_first_failure_sequence P E epsilon C 1 zero_lt_one hnone
  have htone : Tendsto t atTop (𝓝 1) := by
    simpa only [E.lifetime_one] using E.flow.base.tendsto_time_of_scalar_diverges t x ht hR
  obtain ⟨kappa, _hkappa, L, ⟨A⟩⟩ :=
    hextract epsilon C he heA hC g₀ E t x ht hR hprior
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  rcases hcanonical g₀ E t x ht hR L kappa A.certificate 0 le_rfl L.limit.base with
      ⟨N, hcenter, j, hstage⟩ | ⟨N, j, hstage⟩
  · obtain ⟨k, hk⟩ := (blowupSequence_limit_full_neck_canonical P E t x ht hR L kappa
      A.certificate epsilon N he24 hcenter j hstage C).exists
    exact hbad (L.subsequence k) hk
  · obtain ⟨k, hk⟩ := (hcap E NC t x ht htone hR L kappa A.certificate epsilon C₀ N
      heC j hstage).exists
    exact hbad (L.subsequence k) hk

end PoincareConjecture.M35.OrdinaryRealization
