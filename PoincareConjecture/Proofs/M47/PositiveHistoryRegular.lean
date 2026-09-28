import PoincareConjecture.Proofs.M47.PositiveHistoryFlow
import PoincareConjecture.Proofs.M10.ScalarBound
import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem positive_component_curvature_bounded_near
    (hC : RicciFlowCurvatureTheory.{u})
    (E : SurgeryEventData g₀ K P slice metric T)
    [CompactSpace (slice E.tMinus).carrier]
    (v : Ico E.tMinus T) (x : (slice E.tMinus).carrier)
    (hpos : ∀ y ∈ connectedComponent x, ∀ u w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (E.pre_flow.metric v.1) y u w →
        0 < (E.pre_flow.connection v.1).sectionalCurvature y u w)
    {q : (slice E.tMinus).carrier} (hq : q ∈ connectedComponent x)
    (hregular : q ∈ E.regular_limit) :
    ∃ B s : ℝ, s < T ∧ ∀ t ∈ Ioo (max v.1 s) T, ∀ y ∈ connectedComponent x,
      (E.pre_flow.connection t).curvatureTensorNorm y ≤ B := by
  by_contra hbound
  push Not at hbound
  have hfloor := positive_blowup_on_component hC E.pre_flow x v.2.2
    (fun t ht => ⟨v.2.1.trans ht.1, ht.2⟩) hpos hbound
  rw [E.regular_limit_eq] at hregular
  obtain ⟨Bq, hsubsequence⟩ := hregular
  obtain ⟨s, hs, htail⟩ := hfloor (Bq + 1)
  obtain ⟨t, ht, hst, htq⟩ := hsubsequence s hs.2
  have h := htail t ⟨hst, ht.2⟩ q hq
  linarith only [h, htq]

theorem component_subset_regular_of_curvature_tail
    (E : SurgeryEventData g₀ K P slice metric T)
    (v : Ico E.tMinus T) (x : (slice E.tMinus).carrier)
    {B s : ℝ} (hs : s < T)
    (hbound : ∀ t ∈ Ioo (max v.1 s) T, ∀ y ∈ connectedComponent x,
      (E.pre_flow.connection t).curvatureTensorNorm y ≤ B) :
    connectedComponent x ⊆ E.regular_limit := by
  intro y hy
  rw [E.regular_limit_eq]
  refine ⟨9 * B, ?_⟩
  intro t0 ht0
  obtain ⟨t, ht, htT⟩ := exists_between (max_lt (max_lt v.2.2 hs) ht0)
  have hvs : max v.1 s < t := (le_max_left _ _).trans_lt ht
  have hvt : v.1 < t := (le_max_left _ _).trans_lt hvs
  refine ⟨t, ⟨v.2.1.trans hvt.le, htT⟩, (le_max_right _ _).trans_lt ht, ?_⟩
  have hscalar := (le_abs_self ((E.pre_flow.connection t).scalarCurvature y)).trans
    (M10.abs_scalarCurvature_le (E.pre_flow.metric t) (E.pre_flow.connection t) y)
  have hnorm := hbound t ⟨hvs, htT⟩ y hy
  norm_num only [Nat.cast_ofNat, Nat.reducePow] at hscalar
  nlinarith only [hscalar, hnorm]

theorem positive_component_subset_regular
    (hC : RicciFlowCurvatureTheory.{u})
    (E : SurgeryEventData g₀ K P slice metric T)
    [CompactSpace (slice E.tMinus).carrier]
    (v : Ico E.tMinus T) (x : (slice E.tMinus).carrier)
    (hpos : ∀ y ∈ connectedComponent x, ∀ u w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (E.pre_flow.metric v.1) y u w →
        0 < (E.pre_flow.connection v.1).sectionalCurvature y u w)
    {q : (slice E.tMinus).carrier} (hq : q ∈ connectedComponent x)
    (hregular : q ∈ E.regular_limit) :
    connectedComponent x ⊆ E.regular_limit := by
  obtain ⟨B, s, hs, hbound⟩ :=
    positive_component_curvature_bounded_near hC E v x hpos hq hregular
  exact component_subset_regular_of_curvature_tail E v x hs hbound

end PoincareConjecture.M47Positive
