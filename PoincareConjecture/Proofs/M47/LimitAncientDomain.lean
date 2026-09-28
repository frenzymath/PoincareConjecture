import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity











set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47


theorem limitAncient_domain_eq : blowupBackwardInterval ⊤ = Iic 0 := by
  ext t
  simp [blowupBackwardInterval]



def limitAncientFlow (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) :
    RicciFlow 3 L.sliceCarrier.carrier (Iic 0) :=
  Poincare.Geometry.RicciFlow.Harnack.restrictFlow L.flow
    (by rw [limitAncient_domain_eq]) ordConnected_Iic
    ⟨-1, by norm_num, 0, by simp, by norm_num⟩


theorem limitAncientFlow_metric
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
    (limitAncientFlow L).metric t = L.flow.metric t := rfl


theorem limitAncientFlow_connection
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
    HEq ((limitAncientFlow L).connection t) (L.flow.connection t) := HEq.rfl


theorem limitAncientFlow_complete
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) (ht : t ≤ 0) :
    MetricComplete ((limitAncientFlow L).metric t) :=
  L.complete t (by simpa only [limitAncient_domain_eq, mem_Iic] using ht)


theorem limitAncientFlow_nonnegative_curvature_operator
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) (ht : t ≤ 0)
    (x : L.sliceCarrier.carrier) :
    ((limitAncientFlow L).connection t).NonnegativeCurvatureOperator x :=
  L.nonnegative_curvature_operator t
    (by simpa only [limitAncient_domain_eq, mem_Iic] using ht) x



theorem limitAncientFlow_compact_time_bound
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤))
    (I : Set ℝ) (hI : IsCompact I) (hsub : I ⊆ Iic 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∀ x : L.sliceCarrier.carrier,
      |((limitAncientFlow L).connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨B, _, hB⟩ := L.curvature_locally_bounded_in_time I hI
    (by simpa only [limitAncient_domain_eq] using hsub)
  exact ⟨max B 0, le_max_right _ _, fun t ht x => (hB t ht x).trans (le_max_left _ _)⟩


theorem limitAncientFlow_bounded_curvature
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) (ht : t ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.sliceCarrier.carrier,
      |((limitAncientFlow L).connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := limitAncientFlow_compact_time_bound L {t}
    isCompact_singleton (singleton_subset_iff.mpr ht)
  exact ⟨B, hB, hbound t (mem_singleton t)⟩


theorem limitAncientFlow_scalar_normalized
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) :
    ((limitAncientFlow L).connection 0).scalarCurvature L.base = 1 :=
  L.scalar_normalized




theorem limitAncientFlow_noncollapsed
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (κ : ℝ)
    (hnc : BlowupLimitNoncollapsed L κ) :
    AncientKappaNoncollapsed (limitAncientFlow L) κ := by
  intro r₀ _ t ht p r hr _ hcurv
  exact hnc t (by simpa only [limitAncient_domain_eq, mem_Iic] using ht) p r hr
    (by simpa only [limitAncient_domain_eq] using
      (show Ioc (t - r ^ 2) t ⊆ Iic 0 from fun _ hs => hs.2.trans ht)) hcurv

end PoincareConjecture.M47
