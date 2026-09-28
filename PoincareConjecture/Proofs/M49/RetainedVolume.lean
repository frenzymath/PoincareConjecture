import PoincareConjecture.Proofs.M49.RetainedBoundaryVolume
import PoincareConjecture.Proofs.M49.LocalIsometryVolume
import PoincareConjecture.Proofs.M49.RegularLimitDensity










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M49

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}


set_option backward.isDefEq.respectTransparency false in


theorem event_retained_interior_volume_eq
    (E : SurgeryEventData g₀ K P slice metric T) :
    calibratedMetricVolume (metric T) (E.retention.map '' interior E.retained_pre) =
      calibratedMetricVolume E.limit_metric
        (E.limit_identify.map '' interior E.retained_pre) := by
  let L := regionOpenPartialHomeomorph E.limit_identify E.regular_limit_open isOpen_univ
  let U := L '' interior E.retained_pre
  let f := E.retention.map ∘ L.symm
  let j := L ∘ E.retention.inverse
  have hs : interior E.retained_pre ⊆ L.source :=
    interior_subset.trans E.retained_pre_subset
  have hU : IsOpen U := L.isOpen_image_of_subset_source isOpen_interior hs
  have hx (y : E.terminal.carrier) (hy : y ∈ U) : L.symm y ∈ interior E.retained_pre := by
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [L.left_inv (hs hx)]
  have hLd : L.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨E.limit_identify.map_smooth.mdifferentiableOn (by simp),
      E.limit_identify.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    E.retention.map_smooth.comp
      (E.limit_identify.inverse_smooth.mono (subset_univ U))
      (fun y hy => (show L.symm y ∈ E.retained_pre from interior_subset (hx y hy)))
  have hpost : f '' U ⊆ E.retained_post := by
    rintro _ ⟨y, hy, rfl⟩
    exact E.retention.map_image.subset
      ⟨L.symm y, interior_subset (hx y hy), rfl⟩
  have hj : ContMDiffOn (𝓡 3) (𝓡 3) ∞ j (f '' U) :=
    E.limit_identify.map_smooth.comp (E.retention.inverse_smooth.mono hpost)
      (fun y hy => E.retained_pre_subset
        (E.retention.inverse_image.subset ⟨y, hpost hy, rfl⟩))
  have hleft : LeftInvOn j f U := by
    intro y hy
    change L (E.retention.inverse (E.retention.map (L.symm y))) = y
    rw [E.retention.left_inverse (interior_subset (hx y hy)), L.right_inv (mem_univ y)]
  have hmetric (y : E.terminal.carrier) (hy : y ∈ U)
      (a b : TangentSpace (𝓡 3) y) :
      (metric T).inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
        (mfderiv (𝓡 3) (𝓡 3) f y b) = E.limit_metric.inner y a b := by
    have hret : MDifferentiableAt (𝓡 3) (𝓡 3) E.retention.map (L.symm y) :=
      (E.retention.map_smooth.contMDiffAt
        (mem_of_superset (isOpen_interior.mem_nhds (hx y hy)) interior_subset)).mdifferentiableAt
          (by simp)
    have hdf : mfderiv (𝓡 3) (𝓡 3) f y =
        (mfderiv (𝓡 3) (𝓡 3) E.retention.map (L.symm y)).comp
          (mfderiv (𝓡 3) (𝓡 3) L.symm y) :=
      mfderiv_comp y hret (hLd.mdifferentiableAt_symm (mem_univ y))
    have hdi (v : TangentSpace (𝓡 3) y) :
        mfderiv (𝓡 3) (𝓡 3) L (L.symm y)
          (mfderiv (𝓡 3) (𝓡 3) L.symm y v) = v :=
      congrArg (fun D => D v) (hLd.comp_symm_deriv (mem_univ y))
    have hp := E.retained_metric (L.symm y) (interior_subset (hx y hy))
      (mfderiv (𝓡 3) (𝓡 3) L.symm y a) (mfderiv (𝓡 3) (𝓡 3) L.symm y b)
    change (metric T).inner (f y)
      (mfderiv (𝓡 3) (𝓡 3) E.retention.map (L.symm y)
        (mfderiv (𝓡 3) (𝓡 3) L.symm y a))
      (mfderiv (𝓡 3) (𝓡 3) E.retention.map (L.symm y)
        (mfderiv (𝓡 3) (𝓡 3) L.symm y b)) =
      E.limit_metric.inner (L (L.symm y))
        (mfderiv (𝓡 3) (𝓡 3) L (L.symm y)
          (mfderiv (𝓡 3) (𝓡 3) L.symm y a))
        (mfderiv (𝓡 3) (𝓡 3) L (L.symm y)
          (mfderiv (𝓡 3) (𝓡 3) L.symm y b)) at hp
    erw [L.right_inv (mem_univ y), hdi a, hdi b] at hp
    erw [hdf]
    exact hp
  let e := smoothOpenPartialHomeomorph f j U hU hf hj hleft
    (fun y hy => E.limit_metric.mfderiv_bijective_of_pullback_eq
      (metric T) y (hmetric y hy))
  have hvol := calibratedMetricVolume_image_eq_of_partial_isometry
    E.limit_metric (metric T) e (hf.of_le (by simp)) (hj.of_le (by simp))
    hmetric hU.measurableSet (subset_refl U)
  change calibratedMetricVolume (metric T) (f '' U) =
    calibratedMetricVolume E.limit_metric U at hvol
  have himage : f '' U = E.retention.map '' interior E.retained_pre := by
    change f '' (L '' interior E.retained_pre) = _
    rw [image_image]
    apply image_congr
    intro x hx
    change E.retention.map (L.symm (L x)) = E.retention.map x
    rw [L.left_inv (hs hx)]
  rwa [himage] at hvol



theorem event_retained_volume_eq
    (E : SurgeryEventData g₀ K P slice metric T) :
    calibratedMetricVolume (metric T) E.retained_post =
      calibratedMetricVolume E.limit_metric (E.limit_identify.map '' E.retained_pre) := by
  have hR : E.retained_pre = interior E.retained_pre ∪ frontier E.retained_pre := by
    simpa only [E.retained_pre_compact.isClosed.closure_eq] using
      closure_eq_interior_union_frontier E.retained_pre
  have hpost : calibratedMetricVolume (metric T) (E.retention.map '' E.retained_pre) =
      calibratedMetricVolume (metric T) (E.retention.map '' interior E.retained_pre) := by
    apply le_antisymm
    · calc
        _ = calibratedMetricVolume (metric T)
            ((E.retention.map '' interior E.retained_pre) ∪
              (E.retention.map '' frontier E.retained_pre)) := by rw [← image_union, ← hR]
        _ ≤ _ + calibratedMetricVolume (metric T)
            (E.retention.map '' frontier E.retained_pre) := measure_union_le _ _
        _ = _ := by rw [event_post_boundary_volume_eq_zero E, add_zero]
    · exact measure_mono (image_mono interior_subset)
  have hterminal : calibratedMetricVolume E.limit_metric
      (E.limit_identify.map '' E.retained_pre) = calibratedMetricVolume E.limit_metric
        (E.limit_identify.map '' interior E.retained_pre) := by
    apply le_antisymm
    · calc
        _ = calibratedMetricVolume E.limit_metric
            ((E.limit_identify.map '' interior E.retained_pre) ∪
              (E.limit_identify.map '' frontier E.retained_pre)) := by rw [← image_union, ← hR]
        _ ≤ _ + calibratedMetricVolume E.limit_metric
            (E.limit_identify.map '' frontier E.retained_pre) := measure_union_le _ _
        _ = _ := by rw [event_terminal_boundary_volume_eq_zero E, add_zero]
    · exact measure_mono (image_mono interior_subset)
  rw [← E.retention.map_image, hpost, hterminal]
  exact event_retained_interior_volume_eq E

end PoincareConjecture.M49
