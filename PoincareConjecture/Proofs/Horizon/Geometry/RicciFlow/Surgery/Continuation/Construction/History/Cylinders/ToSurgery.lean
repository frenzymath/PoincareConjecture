import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.Slabs
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Events.Separation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M33RegularHistoryRealization

variable {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
  (h : M33RegularHistoryRealization G F) (W : M33RegularHistoryWindow F)
  (hInterval : G.interval = W.interval)
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {J : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder G C origin scale J U) (hJ : J.OrdConnected)
  (htime : ∀ s ∈ J, origin + s / scale ∈ G.interval)

include W hInterval hJ

theorem cylinder_event_coordinates (s : ℝ) (hs : s ∈ J)
    (hT : origin + s / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + s / scale)).carrier]
    (t : ℝ) (ht : t ∈ J)
    (ht' : origin + t / scale ∈
      Ico (F.event (origin + s / scale) hT).tMinus (origin + s / scale))
    (x : C.carrier) (hx : x ∈ U) :
    let E := F.event (origin + s / scale) hT
    let z := (E.pre_identify ⟨origin + t / scale, ht'⟩).symm
      (h.forward (origin + t / scale) (htime t ht) (e.forward t ht x))
    z ∈ interior E.retained_pre ∧
      E.retention.map z = h.forward (origin + s / scale) (htime s hs) (e.forward s hs x) := by
  let E := F.event (origin + s / scale) hT
  have hts : t < s := (div_lt_div_iff_of_pos_right e.scale_pos).mp
    (by linarith [ht'.2])
  obtain ⟨c, z, δ, hδ, hlocal⟩ := e.vertical_compatibility s hs x hx
  obtain ⟨hsc, hscEq⟩ := hlocal s hs (by simpa using hδ)
  obtain ⟨r, hlow, hrs⟩ := exists_between (show max t (s - δ) < s from
    max_lt hts (by linarith))
  have htr : t < r := (le_max_left _ _).trans_lt hlow
  have hδr : |r - s| < δ := by
    rw [abs_of_neg (sub_neg.mpr hrs)]
    have := (le_max_right t (s - δ)).trans_lt hlow
    linarith
  have hrJ : r ∈ J := hJ.out ht hs ⟨htr.le, hrs.le⟩
  obtain ⟨hrc, hrcEq⟩ := hlocal r hrJ hδr
  have hclock_tr : origin + t / scale < origin + r / scale := by
    linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr htr]
  have hclock_rs : origin + r / scale < origin + s / scale := by
    linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hrs]
  have hrpre : origin + r / scale ∈ Ico E.tMinus (origin + s / scale) :=
    ⟨ht'.1.trans hclock_tr.le, hclock_rs⟩
  have hTW : origin + s / scale ∈ W.interval := hInterval ▸ htime s hs
  have hslabTime : Icc (origin + t / scale) (origin + r / scale) ⊆ F.time_domain :=
    F.time_domain_interval.out (h.time_subset (htime t ht)) (h.time_subset (htime r hrJ))
  have hfree : Disjoint F.surgery_times
      (Ioc (origin + t / scale) (origin + r / scale)) := by
    apply (Surgery.RegularHistory.event_pre_surgery_free W hT hTW).mono_right
    intro q hq
    exact ⟨ht'.1.trans_lt hq.1, hq.2.trans_lt hclock_rs⟩
  have hslab := h.cylinder_slab_compatibility e hJ htime
    (origin + t / scale) (origin + r / scale) hclock_tr hslabTime hfree
    t ht r hrJ ⟨le_rfl, hclock_tr.le⟩ ⟨hclock_tr.le, le_rfl⟩ x hx
  have hcoord :
      (E.pre_identify ⟨origin + t / scale, ht'⟩).symm
        (h.forward (origin + t / scale) (htime t ht) (e.forward t ht x)) =
      (E.pre_identify ⟨origin + r / scale, hrpre⟩).symm
        (h.forward (origin + r / scale) (htime r hrJ) (e.forward r hrJ x)) := by
    have hevent := F.event_slab_compatibility (origin + s / scale) hT
      (origin + t / scale) (origin + r / scale) hclock_tr hslabTime hfree
      (origin + t / scale) (origin + r / scale)
      ⟨le_rfl, hclock_tr.le⟩ ⟨hclock_tr.le, le_rfl⟩ ht' hrpre
      ((E.pre_identify ⟨origin + t / scale, ht'⟩).symm
        (h.forward (origin + t / scale) (htime t ht) (e.forward t ht x)))
    rw [Diffeomorph.apply_symm_apply] at hevent
    have heq := congrArg (E.pre_identify ⟨origin + r / scale, hrpre⟩).symm
      (hevent.symm.trans hslab)
    simpa only [E, Diffeomorph.symm_apply_apply] using heq
  have hret := h.pre_retained_at_surgery c (origin + s / scale) hsc hT
    (origin + r / scale) hrc hrpre z
  have hmap := h.surgery_compatibility c (origin + s / scale) hsc hT
    (origin + r / scale) hrc hrpre z
  rw [← hrcEq] at hret
  rw [← hrcEq, ← hscEq] at hmap
  change _ ∈ interior E.retained_pre ∧ E.retention.map _ = _
  rw [hcoord]
  exact ⟨hret, hmap⟩

variable (hRange : ∀ t ht, range (h.forward t ht) = m33RegularRegion F t)

include hRange

def toSurgeryCylinder : SurgeryFlowCylinder F C origin scale J U := by
  refine {
    scale_pos := e.scale_pos
    interval_connected := hJ
    time_subset := ?_
    forward := fun s hs => h.forward (origin + s / scale) (htime s hs) ∘ e.forward s hs
    inverse := fun s hs => e.inverse s hs ∘ h.inverse (origin + s / scale) (htime s hs)
    forward_smooth := fun s hs =>
      (h.forward_smooth _ _).comp_contMDiffOn (e.forward_smooth s hs)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    slab_compatibility := ?_
    retained_at_surgery := ?_
    pre_retained_at_surgery := ?_
    surgery_compatibility := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    exact h.time_subset (htime s hs)
  · intro s hs
    apply (e.inverse_smooth s hs).comp
      ((h.inverse_smooth _ _).mono ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_range_self _
    · rintro _ ⟨x, hx, rfl⟩
      change h.inverse (origin + s / scale) (htime s hs)
        (h.forward (origin + s / scale) (htime s hs) (e.forward s hs x)) ∈ e.forward s hs '' U
      rw [h.left_inverse]
      exact mem_image_of_mem _ hx
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [h.left_inverse, e.left_inverse s hs hx]
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [h.left_inverse, e.left_inverse s hs hx]
  · intro a b hab hJab hfree s hs t ht hs' ht' x hx
    exact h.cylinder_slab_compatibility e hJ htime a b hab hJab hfree
      s hs t ht hs' ht' x hx
  · intro s hs hT _ _
    rintro _ ⟨x, hx, rfl⟩
    have hrange : h.forward (origin + s / scale) (htime s hs) (e.forward s hs x) ∈
        m33RegularRegion F (origin + s / scale) :=
      hRange _ _ ▸ mem_range_self _
    exact hrange hT
  · intro s hs hT _ t ht ht' x hx
    exact (h.cylinder_event_coordinates W hInterval e hJ htime s hs hT t ht ht' x hx).1
  · intro s hs hT _ t ht ht' x hx
    exact (h.cylinder_event_coordinates W hInterval e hJ htime s hs hT t ht ht' x hx).2

@[simp] theorem toSurgeryCylinder_forward (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (h.toSurgeryCylinder W hInterval e hJ htime hRange).forward s hs x =
      h.forward (origin + s / scale) (htime s hs) (e.forward s hs x) := rfl

theorem toSurgeryCylinder_pullbackInner (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    (h.toSurgeryCylinder W hInterval e hJ htime hRange).pullbackInner s hs x v w =
      e.pullbackInner s hs x v w := by
  have he := ((e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hh := (h.forward_smooth (origin + s / scale) (htime s hs)).mdifferentiable
    (by simp) (e.forward s hs x)
  change scale * (F.metric (origin + s / scale)).inner _
    (mfderiv (𝓡 3) (𝓡 3) (h.forward _ _ ∘ e.forward s hs) x v)
    (mfderiv (𝓡 3) (𝓡 3) (h.forward _ _ ∘ e.forward s hs) x w) = _
  rw [mfderiv_comp x hh he]
  exact congrArg (scale * ·) (h.metric_pullback (origin + s / scale) (htime s hs)
    (e.forward s hs x) (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w))

theorem cylinders_to_surgery (hU : IsOpen U) :
    ∃ d : SurgeryFlowCylinder F C origin scale J U,
      (∀ s hs x, x ∈ U → d.forward s hs x =
        h.forward (origin + s / scale) (htime s hs) (e.forward s hs x)) ∧
      (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
        d.pullbackInner s hs x v w = e.pullbackInner s hs x v w) := by
  refine ⟨h.toSurgeryCylinder W hInterval e hJ htime hRange, ?_, ?_⟩
  · intro s hs x _
    rfl
  · intro s hs x hx v w
    exact h.toSurgeryCylinder_pullbackInner W hInterval e hJ htime hRange hU s hs x hx v w

end PoincareConjecture.M33RegularHistoryRealization
