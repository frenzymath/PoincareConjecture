import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T b : ℝ}

theorem retained_composition_invertible
    (event : SurgeryEventData g0 K P slice metric T)
    {V : Set E} (hV : IsOpen V) {A : E → (slice event.tMinus).carrier}
    (hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V)
    (hret : MapsTo A V (interior event.retained_pre))
    (hi : ∀ x ∈ V, (mfderiv (𝓡 3) (𝓡 3) A x).IsInvertible)
    {x : E} (hx : x ∈ V) :
    (mfderiv (𝓡 3) (𝓡 3) (event.retention.map ∘ A) x).IsInvertible := by
  have hlocal := (regionEquivalenceInteriorChart event.retention).isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ (hret hx)
  have hri : (mfderiv (𝓡 3) (𝓡 3) event.retention.map (A x)).IsInvertible :=
    ⟨hlocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hr := event.retention.map_smooth.contMDiffAt
    (mem_interior_iff_mem_nhds.mp (hret hx))
  rw [mfderiv_comp x (hr.mdifferentiableAt (by simp))
    ((hA.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp))]
  exact hri.comp (hi x hx)

theorem retainedPullbackCoefficients_ricci
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (hbirth : G.metric T = metric T)
    {V : Set E} (hV : IsOpen V) {A : E → (slice event.tMinus).carrier}
    (hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V)
    (hret : MapsTo A V (interior event.retained_pre))
    (hi : ∀ x ∈ V, (mfderiv (𝓡 3) (𝓡 3) A x).IsInvertible)
    {t : ℝ} (ht : t ∈ Ioo event.tMinus b) {x : E} (hx : x ∈ V) :
    HasDerivAt (fun s => retainedPullbackCoefficients event G A (s, x))
      (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
        (fun y => retainedPullbackCoefficients event G A (t, y)) x)) t := by
  have hsmooth := retainedPullbackCoefficients_smooth event G hTb hbirth hV hA hret
  have hjets (m : ℕ) := (contDiffOn_spatialJet_within hsmooth
    isOpen_Ioo.uniqueDiffOn hV m).continuousOn
  have hAr : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (event.retention.map ∘ A) V :=
    (event.retention.map_smooth.mono interior_subset).comp hA hret
  have hir := fun y hy => retained_composition_invertible event hV hA hret hi (x := y) hy
  have hinv : ∀ p ∈ Ioo event.tMinus b ×ˢ V,
      (retainedPullbackCoefficients event G A p).IsInvertible := by
    intro p hp
    unfold retainedPullbackCoefficients
    split_ifs
    · exact (event.pre_flow.metric p.1).isInvertible_pullbackCoefficients (hi p.2 hp.2).injective
    · exact (G.metric p.1).isInvertible_pullbackCoefficients (hir p.2 hp.2).injective
  apply hasDerivAt_ricci_coefficients_off_finite isOpen_Ioo (finite_singleton T)
    hsmooth.continuousOn hjets hinv _ ht hx
  intro s hs hnot y hy
  have hne : s ≠ T := by simpa only [mem_singleton_iff] using hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let H := Poincare.Geometry.RicciFlow.Harnack.restrictFlow event.pre_flow
      Ioo_subset_Ico_self ordConnected_Ioo (Ioo_infinite event.tMinus_lt).nontrivial
    have hd := hasDerivAt_pullbackCoefficients_ricci H isOpen_Ioo hV hA hi ⟨hs.1, hlt⟩ hy
    have heq : (fun r => retainedPullbackCoefficients event G A (r, y)) =ᶠ[𝓝 s]
        (fun r => (H.metric r).pullbackCoefficients A y) := by
      filter_upwards [Iio_mem_nhds hlt] with r hr
      change r < T at hr
      simp only [retainedPullbackCoefficients, if_pos hr, H,
        Poincare.Geometry.RicciFlow.Harnack.restrictFlow]
    simpa only [retainedPullbackCoefficients, if_pos hlt, H,
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow] using
        hd.congr_of_eventuallyEq heq
  · let H := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G
      Ioo_subset_Icc_self ordConnected_Ioo (Ioo_infinite hTb).nontrivial
    have hd := hasDerivAt_pullbackCoefficients_ricci H isOpen_Ioo hV hAr hir ⟨hgt, hs.2⟩ hy
    have heq : (fun r => retainedPullbackCoefficients event G A (r, y)) =ᶠ[𝓝 s]
        (fun r => (H.metric r).pullbackCoefficients (event.retention.map ∘ A) y) := by
      filter_upwards [Ioi_mem_nhds hgt] with r hr
      change T < r at hr
      simp only [retainedPullbackCoefficients, if_neg (not_lt_of_gt hr), H,
        Poincare.Geometry.RicciFlow.Harnack.restrictFlow]
    simpa only [retainedPullbackCoefficients, if_neg (not_lt_of_gt hgt), H,
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow] using
        hd.congr_of_eventuallyEq heq

end PoincareConjecture.M44
