import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.RadialAnnulusComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.UnitTimeCanonical

/-!
# Uniform full radial-neck comparison in the actual flow

Morgan-Tian Theorem 12.32, pp. 326-327. The independently checked
unit-time canonical control supplies every earlier certificate needed
for actual ancient compactness. A failure sequence with divergent
scalar and normalized tip distance contradicts its literal radial
annulus comparison, with the requested epsilon unchanged.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.32: one actual scalar and normalized tip-distance
threshold supplies the full intrinsic radial-annulus comparison. -/
theorem exists_radial_annulus_comparison_threshold
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ B : ℝ, 0 < B ∧ ∀ t, ∀ ht : t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace, B ≤ (E.flow.connection t).scalarCurvature x →
        B ≤ ((E.flow.metric t).edist 0 x).toReal *
          Real.sqrt ((E.flow.connection t).scalarCurvature x) →
        RadialAnnulusComparison E t ht x epsilon := by
  classical
  obtain ⟨delta, hdelta, hcanonical⟩ := exists_unit_time_canonical_constants P
  obtain ⟨deltaA, hdeltaA, hextract⟩ := exists_ancient_extraction_threshold P
  let eta := min delta deltaA
  have heta : 0 < eta := lt_min hdelta hdeltaA
  obtain ⟨C, H, hC, hH, hgood⟩ := hcanonical eta heta (min_le_left _ _) E
  by_contra hnone
  push Not at hnone
  have hselect (k : ℕ) := hnone (H + (k : ℝ) + 1) (by positivity)
  choose t ht x hscalar hdistance hbad using hselect
  have hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k))
      atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (b - H - 1)] with k hk
    linarith [hscalar k]
  have hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (b - H - 1)] with k hk
    linarith [hdistance k]
  have hprior : ∀ k, generalizedEarlierStrongCanonicalNeighborhoods
      ((blowupSequence P E t x ht hR).flow k) eta C
      ((blowupSequence P E t x ht hR).base k).1
      ((blowupSequence P E t x ht hR).base k).2 := by
    intro k s hs _hst y hhigh
    have hscale := scalar_eq P E.flow.base.flow (ht k) (x k)
    have hvalue := scalar_eq P E.flow.base.flow hs y.val
    have hhigh' : 4 * (E.flow.connection (t k)).scalarCurvature (x k) ≤
        (E.flow.connection s).scalarCurvature y.val :=
      (congrArg (fun r : ℝ => 4 * r) hscale).symm ▸ (hvalue ▸ hhigh)
    have hthreshold : H ≤ (E.flow.connection s).scalarCurvature y.val := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith only [hH, hscalar k, hk, hhigh']
    exact ⟨hgood s hs y.val hthreshold⟩
  obtain ⟨kappa, _hkappa, L, ⟨A⟩⟩ :=
    hextract eta C heta (min_le_right _ _) hC g₀ E t x ht hR hprior
  obtain ⟨k, hk⟩ := (blowupSequence_radial_annulus_comparison P E t x ht hR hd L
    A.certificate epsilon he).exists
  exact hbad (L.subsequence k) hk

end PoincareMT.M35.OrdinaryRealization
