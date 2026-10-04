import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
# Coherent closed slabs inside an ordinary half-open interval

The maps and metrics are the raw flow's own closed slabs. Their initial
identities and transport coherence determine them on every common time.
The left endpoint may itself be a surgery time.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M51Slab

variable (F : SurgeryFlowData.{u}) {a H : ℝ} (haH : a < H)
    (hI : Set.Ico a H ⊆ F.time_domain)
    (hS : Disjoint F.surgery_times (Set.Ioo a H))

/-- A closed ordinary slab strictly before the excluded right endpoint. -/
noncomputable def closedSlab (b : ℝ) (hab : a < b) (hbH : b < H) :
    SurgeryRegularSlab F.slice F.metric a b :=
  F.regular_slabs a b hab
    (fun _ ht => hI ⟨ht.1, ht.2.trans_lt hbH⟩)
    (hS.mono_right (show Set.Ioc a b ⊆ Set.Ioo a H from
      fun _ ht => ⟨ht.1, ht.2.trans_lt hbH⟩))

include hI hS

theorem closedSlab_initial_inverse (b : ℝ) (hab : a < b) (hbH : b < H)
    (x : (F.slice a).carrier) :
    ((closedSlab F hI hS b hab hbH).identify ⟨a, le_rfl, hab.le⟩).symm x = x := by
  have h := ((closedSlab F hI hS b hab hbH).identify
    ⟨a, le_rfl, hab.le⟩).symm_apply_apply x
  rw [(closedSlab F hI hS b hab hbH).initial_identify] at h
  exact h

/-- Two slabs with the same initial time have the same complete spatial map. -/
theorem closedSlab_identify_eq (b c : ℝ) (hab : a < b) (hbH : b < H)
    (hac : a < c) (hcH : c < H) (t : ℝ) (htb : t ∈ Set.Icc a b)
    (htc : t ∈ Set.Icc a c) :
    ⇑((closedSlab F hI hS b hab hbH).identify ⟨t, htb⟩) =
      (closedSlab F hI hS c hac hcH).identify ⟨t, htc⟩ := by
  funext x
  have h := F.slab_transport_coherent a b a c hab
    (fun _ ht => hI ⟨ht.1, ht.2.trans_lt hbH⟩)
    (hS.mono_right (show Set.Ioc a b ⊆ Set.Ioo a H from
      fun _ ht => ⟨ht.1, ht.2.trans_lt hbH⟩)) hac
    (fun _ ht => hI ⟨ht.1, ht.2.trans_lt hcH⟩)
    (hS.mono_right (show Set.Ioc a c ⊆ Set.Ioo a H from
      fun _ ht => ⟨ht.1, ht.2.trans_lt hcH⟩)) a t
    ⟨le_rfl, hab.le⟩ htb ⟨le_rfl, hac.le⟩ htc x
  change (closedSlab F hI hS b hab hbH).transport ⟨a, le_rfl, hab.le⟩ ⟨t, htb⟩ x =
    (closedSlab F hI hS c hac hcH).transport ⟨a, le_rfl, hac.le⟩ ⟨t, htc⟩ x at h
  simpa only [SurgeryRegularSlab.transport,
    closedSlab_initial_inverse F hI hS b hab hbH x,
    closedSlab_initial_inverse F hI hS c hac hcH x] using h

/-- Equality of the actual pullbacks gives metric equality, not equality of
the retained connection records. -/
theorem closedSlab_metric_eq (b c : ℝ) (hab : a < b) (hbH : b < H)
    (hac : a < c) (hcH : c < H) (t : ℝ) (htb : t ∈ Set.Icc a b)
    (htc : t ∈ Set.Icc a c) :
    (closedSlab F hI hS b hab hbH).flow.metric t =
      (closedSlab F hI hS c hac hcH).flow.metric t := by
  have he := closedSlab_identify_eq F hI hS b c hab hbH hac hcH t htb htc
  have hinner : ∀ x v w,
      ((closedSlab F hI hS b hab hbH).flow.metric t).inner x v w =
        ((closedSlab F hI hS c hac hcH).flow.metric t).inner x v w := by
    intro x v w
    rw [← (closedSlab F hI hS b hab hbH).metric_pullback ⟨t, htb⟩,
      ← (closedSlab F hI hS c hac hcH).metric_pullback ⟨t, htc⟩, he]
  cases h₁ : (closedSlab F hI hS b hab hbH).flow.metric t
  cases h₂ : (closedSlab F hI hS c hac hcH).flow.metric t
  rw [h₁, h₂] at hinner
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact hinner x v w

end PoincareMT.M51Slab
