import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.RegularSlices

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}

def SlabCompatible (A : GeneralizedRicciFlowBox (slice W) (metric W) W.interval) : Prop :=
  ∀ a b : ℝ, ∀ hab : a < b, ∀ hJ : Icc a b ⊆ F.time_domain,
    ∀ hfree : Disjoint F.surgery_times (Ioc a b),
    ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ A.interval, ∀ ht' : t ∈ A.interval,
    ∀ x : A.carrier.carrier,
      (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        (forward W s (A.forward s hs' x)) = forward W t (A.forward t ht' x)

theorem boxes_vertical_of_regular_overlap
    (A B : GeneralizedRicciFlowBox (slice W) (metric W) W.interval)
    (hA : SlabCompatible A) (hB : SlabCompatible B)
    (hfree : Disjoint F.surgery_times (A.interval ∩ B.interval))
    (t : ℝ) (htA : t ∈ A.interval) (htB : t ∈ B.interval)
    (x : A.carrier.carrier) (y : B.carrier.carrier)
    (hxy : A.forward t htA x = B.forward t htB y)
    (s : ℝ) (hsA : s ∈ A.interval) (hsB : s ∈ B.interval) :
    A.forward s hsA x = B.forward s hsB y := by
  by_cases hst : s = t
  · subst s
    exact hxy
  have hab : min s t < max s t := min_lt_max.mpr hst
  have hsubA : Icc (min s t) (max s t) ⊆ A.interval := by
    simpa only [Icc_min_max] using
      A.flow.interval.uIcc_subset hsA htA
  have hsubB : Icc (min s t) (max s t) ⊆ B.interval := by
    simpa only [Icc_min_max] using
      B.flow.interval.uIcc_subset hsB htB
  have hAW : A.interval ⊆ W.interval := by
    obtain ⟨U, _, hU⟩ := A.relatively_open
    rw [hU]
    exact inter_subset_left
  have hJ := (hsubA.trans hAW).trans W.time_subset
  have hreg : Disjoint F.surgery_times (Ioc (min s t) (max s t)) := by
    apply hfree.mono_right
    intro r hr
    exact ⟨hsubA ⟨hr.1.le, hr.2⟩, hsubB ⟨hr.1.le, hr.2⟩⟩
  have hts : t ∈ Icc (min s t) (max s t) := ⟨min_le_right _ _, le_max_right _ _⟩
  have hss : s ∈ Icc (min s t) (max s t) := ⟨min_le_left _ _, le_max_left _ _⟩
  apply (forward_openEmbedding W s).injective
  rw [← hA _ _ hab hJ hreg t s hts hss htA hsA x,
    ← hB _ _ hab hJ hreg t s hts hss htB hsB y, hxy]

end PoincareConjecture.Surgery.RegularHistory
