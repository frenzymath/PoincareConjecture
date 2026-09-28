import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderTimeCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderPreterminalCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderRetainedCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedPullbackRicci
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

theorem regularSlab_initial_metric (F : SurgeryFlowData.{u})
    {a b : ℝ} (S : SurgeryRegularSlab F.slice F.metric a b) :
    S.flow.metric a = F.metric a := by
  have h : (S.flow.metric a).inner = (F.metric a).inner := by
    funext x
    ext v w
    exact regularSlab_initial_inner F S x v w
  cases h1 : S.flow.metric a
  cases h2 : F.metric a
  rw [h1, h2] at h
  congr

theorem cylinderTimeCoefficients_eq_event
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    (r0 : ℝ) (hr0 : r0 ∈ I)
    (c : ℝ) (hc : c ∈ I) (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hfree : Disjoint F.surgery_times
      (Ioo (F.event (origin + c / scale) hT).tMinus (origin + c / scale)))
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    {b : ℝ} (hTb : origin + c / scale < b)
    (hJ : Icc (origin + c / scale) b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc (origin + c / scale) b))
    {t : ℝ} (ht : scale * (t - origin) ∈ I)
    (ht' : t ∈ Ioo (F.event (origin + c / scale) hT).tMinus b)
    {x : E} (hx : x ∈ V) :
    cylinderTimeCoefficients e f r0 hr0 (t, x) =
      retainedPullbackCoefficients (F.event (origin + c / scale) hT)
        (F.regular_slabs (origin + c / scale) b hTb hJ hNo).flow
        (((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f) (t, x) := by
  by_cases hbefore : t < origin + c / scale
  · have htpre : origin + (scale * (t - origin)) / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale) := by
      rw [cylinder_clock_parameter e]
      exact ⟨ht'.1.le, hbefore⟩
    simpa only [cylinderTimeCoefficients, dif_pos ht, retainedPullbackCoefficients,
      if_pos hbefore, cylinder_clock_parameter e] using
        cylinderPhysicalCoefficients_eq_preterminal e hV hf hmap hT hfree r hr hr'
          _ ht htpre hx
  · have htafter : origin + (scale * (t - origin)) / scale ∈ Icc (origin + c / scale) b := by
      rw [cylinder_clock_parameter e]
      exact ⟨le_of_not_gt hbefore, ht'.2.le⟩
    simpa only [cylinderTimeCoefficients, dif_pos ht, retainedPullbackCoefficients,
      if_neg hbefore, cylinder_clock_parameter e] using
        cylinderPhysicalCoefficients_eq_retained e hV hf hmap c hc hT r hr hr'
          hTb hJ hNo _ ht htafter hx

theorem cylinderTimeCoefficients_event_smooth_ricci
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U)
    (r0 : ℝ) (hr0 : r0 ∈ I)
    (c : ℝ) (hc : c ∈ I) (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hfree : Disjoint F.surgery_times
      (Ioo (F.event (origin + c / scale) hT).tMinus (origin + c / scale)))
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    {b : ℝ} (hTb : origin + c / scale < b)
    (hJ : Icc (origin + c / scale) b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc (origin + c / scale) b))
    {J : Set ℝ} (hJI : ∀ t ∈ J, scale * (t - origin) ∈ I)
    (hJevent : J ⊆ Ioo (F.event (origin + c / scale) hT).tMinus b) :
    ContDiffOn ℝ ∞ (cylinderTimeCoefficients e f r0 hr0) (J ×ˢ f.source) ∧
      ∀ t ∈ J, ∀ x ∈ f.source,
        HasDerivWithinAt (fun s => cylinderTimeCoefficients e f r0 hr0 (s, x))
          (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
            (fun y => cylinderTimeCoefficients e f r0 hr0 (t, y)) x)) J t := by
  let event := F.event (origin + c / scale) hT
  let S := F.regular_slabs (origin + c / scale) b hTb hJ hNo
  let A := (event.pre_identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f
  have hfmap : MapsTo f f.source U := fun _ hx => hmap (f.map_source hx)
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A f.source :=
    (event.pre_identify ⟨origin + r / scale, hr'⟩).symm.contMDiff.comp_contMDiffOn
      ((e.forward_smooth r hr).comp f.contMDiffOn hfmap)
  have hret : MapsTo A f.source (interior event.retained_pre) :=
    fun x hx => e.pre_retained_at_surgery c hc hT r hr hr' (f x) (hfmap hx)
  have hi : ∀ x ∈ f.source, (mfderiv (𝓡 3) (𝓡 3) A x).IsInvertible := by
    intro x hx
    let d := (f.trans (cylinderSliceChart e hU r hr)).trans
      (event.pre_identify ⟨origin + r / scale, hr'⟩).symm.toPartialDiffeomorph
    have hxd : x ∈ d.source := ⟨⟨hx, hfmap hx⟩, mem_univ _⟩
    exact ⟨(d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxd).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  have hbirth := regularSlab_initial_metric F S
  have heq (t : ℝ) (ht : t ∈ J) (x : E) (hx : x ∈ f.source) :
      cylinderTimeCoefficients e f r0 hr0 (t, x) =
        retainedPullbackCoefficients event S.flow A (t, x) :=
    cylinderTimeCoefficients_eq_event e f.open_source f.contMDiffOn hfmap r0 hr0
      c hc hT hfree r hr hr' hTb hJ hNo (hJI t ht) (hJevent ht) hx
  refine ⟨?_, ?_⟩
  · exact ((retainedPullbackCoefficients_smooth event S.flow hTb hbirth f.open_source hA hret).mono
      (prod_mono hJevent Subset.rfl)).congr (fun p hp => heq p.1 hp.1 p.2 hp.2)
  · intro t ht x hx
    have hgerm : (fun y => cylinderTimeCoefficients e f r0 hr0 (t, y)) =ᶠ[𝓝 x]
        (fun y => retainedPullbackCoefficients event S.flow A (t, y)) := by
      filter_upwards [f.open_source.mem_nhds hx] with y hy
      exact heq t ht y hy
    rw [SpacetimeBounds.metricTwoJet_congr_of_eventuallyEq hgerm]
    exact (retainedPullbackCoefficients_ricci event S.flow hTb hbirth f.open_source hA hret hi
      (hJevent ht) hx).hasDerivWithinAt.congr_of_mem (fun s hs => heq s hs x hx) ht

end PoincareConjecture.M44
