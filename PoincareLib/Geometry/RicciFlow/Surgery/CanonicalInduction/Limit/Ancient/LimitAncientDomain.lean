import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity

/-!
# The literal infinite-horizon limit flow

The infinite backward domain is exactly the closed ancient interval. Its
restriction keeps the actual metric and connection, and compact singleton
time sets give the required separate slice bounds.
Source: Morgan--Tian Proposition 17.1, pp. 407-408; reviewed derivation
`proof-work/tasks/M47/derivations/limit-ancient-identification.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.M47

/-- The infinite backward horizon includes every nonpositive real time. -/
theorem limitAncient_domain_eq : blowupBackwardInterval ⊤ = Iic 0 := by
  ext t
  simp [blowupBackwardInterval]

/-- Restriction along the exact ancient domain equality retains the total
metric and connection representatives of the actual limit. -/
def limitAncientFlow (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) :
    RicciFlow 3 L.sliceCarrier.carrier (Iic 0) :=
  Poincare.Geometry.RicciFlow.Harnack.restrictFlow L.flow
    (by rw [limitAncient_domain_eq]) ordConnected_Iic
    ⟨-1, by norm_num, 0, by simp, by norm_num⟩

/-- The ancient flow's selected metric is literally the limit metric. -/
theorem limitAncientFlow_metric
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
    (limitAncientFlow L).metric t = L.flow.metric t := rfl

/-- The dependent connection family is retained together with the metric. -/
theorem limitAncientFlow_connection
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
    HEq ((limitAncientFlow L).connection t) (L.flow.connection t) := HEq.rfl

/-- Completeness concerns the same selected metric and induced distance. -/
theorem limitAncientFlow_complete
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) (ht : t ≤ 0) :
    MetricComplete ((limitAncientFlow L).metric t) :=
  L.complete t (by simpa only [limitAncient_domain_eq, mem_Iic] using ht)

/-- The actual limit's nonnegative curvature operator is unchanged. -/
theorem limitAncientFlow_nonnegative_curvature_operator
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) (ht : t ≤ 0)
    (x : L.sliceCarrier.carrier) :
    ((limitAncientFlow L).connection t).NonnegativeCurvatureOperator x :=
  L.nonnegative_curvature_operator t
    (by simpa only [limitAncient_domain_eq, mem_Iic] using ht) x

/-- A nonnegative curvature ceiling on one compact set of ancient times;
the ceiling is allowed to depend on that set. -/
theorem limitAncientFlow_compact_time_bound
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤))
    (I : Set ℝ) (hI : IsCompact I) (hsub : I ⊆ Iic 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∀ x : L.sliceCarrier.carrier,
      |((limitAncientFlow L).connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨B, _, hB⟩ := L.curvature_locally_bounded_in_time I hI
    (by simpa only [limitAncient_domain_eq] using hsub)
  exact ⟨max B 0, le_max_right _ _, fun t ht x => (hB t ht x).trans (le_max_left _ _)⟩

/-- Singleton compactness gives a bound on each individual ancient slice. -/
theorem limitAncientFlow_bounded_curvature
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (t : ℝ) (ht : t ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.sliceCarrier.carrier,
      |((limitAncientFlow L).connection t).curvatureTensorNorm x| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := limitAncientFlow_compact_time_bound L {t}
    isCompact_singleton (singleton_subset_iff.mpr ht)
  exact ⟨B, hB, hbound t (mem_singleton t)⟩

/-- The terminal scalar normalization holds for this exact ancient flow. -/
theorem limitAncientFlow_scalar_normalized
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) :
    ((limitAncientFlow L).connection 0).scalarCurvature L.base = 1 :=
  L.scalar_normalized

/-- Literal all-scale limit noncollapse supplies the ancient predicate on
the same metric balls and calibrated volumes. Its geometric producer is
an upstream obligation. -/
theorem limitAncientFlow_noncollapsed
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) (κ : ℝ)
    (hnc : BlowupLimitNoncollapsed L κ) :
    AncientKappaNoncollapsed (limitAncientFlow L) κ := by
  intro r₀ _ t ht p r hr _ hcurv
  exact hnc t (by simpa only [limitAncient_domain_eq, mem_Iic] using ht) p r hr
    (by simpa only [limitAncient_domain_eq] using
      (show Ioc (t - r ^ 2) t ⊆ Iic 0 from fun _ hs => hs.2.trans ht)) hcurv

end PoincareMT.M47
