import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedTimeJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import Mathlib.Order.Interval.Set.Infinite










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T b : ℝ}




theorem retained_inverse_coordinates_invertible
    (event : SurgeryEventData g0 K P slice metric T)
    (q : (slice event.tMinus).carrier) {U : Set E}
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre)
    {x : E} (hx : x ∈ U) :
    (mfderiv (𝓡 3) (𝓡 3)
      (event.retention.map ∘ (extChartAt (𝓡 3) q).symm) x).IsInvertible := by
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds (hchart hx))
  have hretx := hret (mem_image_of_mem _ hx)
  have hr := event.retention.map_smooth.contMDiffAt
    (mem_interior_iff_mem_nhds.mp hretx)
  have hi : (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm x).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (hchart hx)
  have hl := (regionEquivalenceInteriorChart event.retention).isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ hretx
  have hj : (mfderiv (𝓡 3) (𝓡 3) event.retention.map
      ((extChartAt (𝓡 3) q).symm x)).IsInvertible :=
    ⟨hl.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  rw [mfderiv_comp x (hr.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  exact hj.comp hi




theorem retainedChartCoefficients_equation_away
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (q : (slice event.tMinus).carrier) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre)
    {t : ℝ} (ht : t ∈ Ioo event.tMinus b) (hne : t ≠ T)
    {x : E} (hx : x ∈ U) :
    HasDerivAt (fun s => retainedChartCoefficients event G q (s, x))
      (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
        (fun y => retainedChartCoefficients event G q (t, y)) x)) t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow event.pre_flow
      Ioo_subset_Ico_self ordConnected_Ioo (Ioo_infinite event.tMinus_lt).nontrivial
    have hi (y : E) (hy : y ∈ U) :
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hchart hy)
    have hd := hasDerivAt_pullbackCoefficients_ricci F isOpen_Ioo hU
      ((contMDiffOn_extChartAt_symm q).mono hchart) hi ⟨ht.1, hlt⟩ hx
    have heq : (fun s => retainedChartCoefficients event G q (s, x)) =ᶠ[𝓝 t]
        (fun s => (F.metric s).pullbackCoefficients (extChartAt (𝓡 3) q).symm x) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      change s < T at hs
      simp only [retainedChartCoefficients, if_pos hs, F,
        Poincare.Geometry.RicciFlow.Harnack.restrictFlow]
    simpa only [retainedChartCoefficients, if_pos hlt, F,
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow] using
        hd.congr_of_eventuallyEq heq
  · let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G
      Ioo_subset_Icc_self ordConnected_Ioo (Ioo_infinite hTb).nontrivial
    have he := retained_inverse_coordinates_smooth event q hchart hret
    have hi := fun y hy => retained_inverse_coordinates_invertible event q hchart hret
      (x := y) hy
    have hd := hasDerivAt_pullbackCoefficients_ricci F isOpen_Ioo hU he hi ⟨hgt, ht.2⟩ hx
    have heq : (fun s => retainedChartCoefficients event G q (s, x)) =ᶠ[𝓝 t]
        (fun s => (F.metric s).pullbackCoefficients
          (event.retention.map ∘ (extChartAt (𝓡 3) q).symm) x) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      change T < s at hs
      simp only [retainedChartCoefficients, if_neg (not_lt_of_gt hs), F,
        Poincare.Geometry.RicciFlow.Harnack.restrictFlow]
    simpa only [retainedChartCoefficients, if_neg (not_lt_of_gt hgt), F,
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow] using
        hd.congr_of_eventuallyEq heq




theorem retainedChartCoefficients_invertible
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) {U : Set E}
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre)
    (t : ℝ) {x : E} (hx : x ∈ U) :
    (retainedChartCoefficients event G q (t, x)).IsInvertible := by
  unfold retainedChartCoefficients
  split_ifs
  · exact (event.pre_flow.metric t).isInvertible_chartCoefficients q (hchart hx)
  · exact (G.metric t).isInvertible_pullbackCoefficients
      (retained_inverse_coordinates_invertible event q hchart hret hx).injective




theorem retainedChartCoefficients_smooth_ricci
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (hbirth : G.metric T = metric T)
    (q : (slice event.tMinus).carrier) (hq : q ∈ interior event.retained_pre)
    {U : Set E} (hU : IsOpen U) (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre) :
    ContDiffOn ℝ ∞ (retainedChartCoefficients event G q) (Ioo event.tMinus b ×ˢ U) ∧
      ∀ t ∈ Ioo event.tMinus b, ∀ x ∈ U,
        HasDerivAt (fun s => retainedChartCoefficients event G q (s, x))
          (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
            (fun y => retainedChartCoefficients event G q (t, y)) x)) t := by
  have hjets := retainedChartCoefficients_continuous_spatialJets
    event G hTb hbirth q hq hU hchart hret
  have hsides : ContDiffOn ℝ ∞ (retainedChartCoefficients event G q)
      ((Ioo event.tMinus b \ {T}) ×ˢ U) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hne : t ≠ T := by simpa only [mem_singleton_iff] using ht.2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ((retainedChartCoefficients_smooth_before event G q hU hchart).contDiffAt
        ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨ht.1.1, hlt⟩, hx⟩)).contDiffWithinAt
    · have hs := (retainedChartCoefficients_smooth_after event G q hU hchart hret).mono
        (prod_mono Ioo_subset_Ico_self Subset.rfl)
      exact (hs.contDiffAt
        ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨hgt, ht.1.2⟩, hx⟩)).contDiffWithinAt
  have hinv : ∀ p ∈ Ioo event.tMinus b ×ˢ U,
      (retainedChartCoefficients event G q p).IsInvertible :=
    fun p hp => retainedChartCoefficients_invertible event G q hchart hret p.1 hp.2
  have hevol : ∀ t ∈ Ioo event.tMinus b, t ∉ ({T} : Set ℝ) → ∀ x ∈ U,
      HasDerivAt (fun s => retainedChartCoefficients event G q (s, x))
        (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
          (fun y => retainedChartCoefficients event G q (t, y)) x)) t := by
    intro t ht hnot x hx
    exact retainedChartCoefficients_equation_away event G hTb q hU hchart hret ht
      (by simpa only [mem_singleton_iff] using hnot) hx
  have hs := contDiffOn_ricci_coefficients_off_finite isOpen_Ioo hU (finite_singleton T)
    hsides (fun t _ => retainedChartCoefficients_spatial_smooth event G q hU hchart hret t)
    hjets hinv hevol
  refine ⟨hs, ?_⟩
  intro t ht x hx
  exact hasDerivAt_ricci_coefficients_off_finite isOpen_Ioo (finite_singleton T)
    hs.continuousOn hjets hinv hevol ht hx

end PoincareConjecture.M44
