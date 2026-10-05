import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas

/-!
# Identifying the generalized atlas with the old surgery history

The constructed spacetime retains the original ordinary transports and the
actual retention map at every old event, including the pre-retained region.
Source: Morgan--Tian, Lemma 14.11 and Proposition 14.12, pp. 349-350.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  (L : ∀ t, t ∈ F.surgery_times → t ∈ W.interval →
    RicciFlowLocalTheory 3 (F.slice t).carrier)

theorem atlasBox_pre_retained (i : BoxIndex W) (t : ℝ)
    (ht : t ∈ (atlasBox W L i).interval) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (s : ℝ) (hs : s ∈ (atlasBox W L i).interval)
    (hs' : s ∈ Ico (F.event t hT).tMinus t) (x : (atlasBox W L i).carrier.carrier) :
    ((F.event t hT).pre_identify ⟨s, hs'⟩).symm
      (forward W s ((atlasBox W L i).forward s hs x)) ∈
        interior (F.event t hT).retained_pre := by
  cases i with
  | inl a => exact (a.down.val.regular ht hT).elim
  | inr e =>
    let := W.slice_nonempty e.down.val e.down.property.2
    have he := (eventWindow W e.down).box_events_unique
      (L _ e.down.property.1 e.down.property.2) ht hT
    subst t
    change ((F.event e.down.val e.down.property.1).pre_identify ⟨s, hs'⟩).symm
      (forward W s ((eventWindow W e.down).identify s hs x)) ∈ _
    rw [(eventWindow W e.down).identify_of_pre s hs hs'.2]
    simp only [EventIdentify.pre, forward, Diffeomorph.symm_apply_apply]
    exact x.property

theorem atlasBox_surgery_compatibility (i : BoxIndex W) (t : ℝ)
    (ht : t ∈ (atlasBox W L i).interval) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (s : ℝ) (hs : s ∈ (atlasBox W L i).interval)
    (hs' : s ∈ Ico (F.event t hT).tMinus t) (x : (atlasBox W L i).carrier.carrier) :
    (F.event t hT).retention.map
      (((F.event t hT).pre_identify ⟨s, hs'⟩).symm
        (forward W s ((atlasBox W L i).forward s hs x))) =
      forward W t ((atlasBox W L i).forward t ht x) := by
  cases i with
  | inl a => exact (a.down.val.regular ht hT).elim
  | inr e =>
    let := W.slice_nonempty e.down.val e.down.property.2
    have he := (eventWindow W e.down).box_events_unique
      (L _ e.down.property.1 e.down.property.2) ht hT
    subst t
    change (F.event e.down.val e.down.property.1).retention.map
      (((F.event e.down.val e.down.property.1).pre_identify ⟨s, hs'⟩).symm
        (forward W s ((eventWindow W e.down).identify s hs x))) =
      forward W e.down.val ((eventWindow W e.down).identify e.down.val ht x)
    rw [(eventWindow W e.down).identify_of_pre s hs hs'.2]
    simp only [EventIdentify.pre, forward, Diffeomorph.symm_apply_apply]
    exact ((eventWindow W e.down).forward_identify_event x).symm

/-- Realize the complete old transports and event maps in the constructed atlas. -/
def realization : M33RegularHistoryRealization (generalized W L) F where
  time_subset := W.time_subset
  forward t _ := forward W t
  inverse := inverse W
  forward_openEmbedding t _ := forward_openEmbedding W t
  forward_smooth t _ := forward_smooth W t
  inverse_smooth := inverse_smooth W
  left_inverse := left_inverse W
  right_inverse := right_inverse W
  metric_pullback t _ := metric_pullback W t
  slab_compatibility := atlasBox_slab_compatibility W L
  retained_at_surgery i t ht hT _ _ x :=
    ((atlasBox W L i).forward t ht x).property.2 hT
  pre_retained_at_surgery := atlasBox_pre_retained W L
  surgery_compatibility := atlasBox_surgery_compatibility W L

end PoincareMT.Surgery.RegularHistory
