import PoincareConjecture.Definitions.Ch15.SurgeryContinuation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}

theorem cylinder_slab_compatibility (d : SurgeryFlowCylinder F C a q J U)
    (l r : ℝ) (hlr : l < r) (hJ : Icc l r ⊆ E.extended.time_domain)
    (hfree : Disjoint E.extended.surgery_times (Ioc l r))
    (s : ℝ) (hs : s ∈ J) (t : ℝ) (ht : t ∈ J)
    (hs' : a + s / q ∈ Icc l r) (ht' : a + t / q ∈ Icc l r)
    (x : C.carrier) (hx : x ∈ U) :
    (E.extended.regular_slabs l r hlr hJ hfree).transport
        ⟨a + s / q, hs'⟩ ⟨a + t / q, ht'⟩
        (E.identify (a + s / q) (d.time_subset ⟨s, hs, rfl⟩) (d.forward s hs x)) =
      E.identify (a + t / q) (d.time_subset ⟨t, ht, rfl⟩) (d.forward t ht x) := by
  by_cases hclock : a + s / q = a + t / q
  · have hst : s = t := by
      have hdiv : s / q = t / q := add_left_cancel hclock
      simpa only [div_mul_cancel₀ _ d.scale_pos.ne'] using
        congrArg (fun z : ℝ => z * q) hdiv
    subst t
    simp [SurgeryRegularSlab.transport]
  · let b := min (a + s / q) (a + t / q)
    let c := max (a + s / q) (a + t / q)
    have hbc : b < c := min_lt_max.mpr hclock
    have hold : Icc b c ⊆ F.time_domain :=
      F.time_domain_interval.uIcc_subset (d.time_subset ⟨s, hs, rfl⟩)
        (d.time_subset ⟨t, ht, rfl⟩)
    have hin : Ioc b c ⊆ Ioc l r := by
      intro z hz
      exact ⟨lt_of_le_of_lt (le_min hs'.1 ht'.1) hz.1,
        hz.2.trans (max_le hs'.2 ht'.2)⟩
    have hnewfree : Disjoint E.extended.surgery_times (Ioc b c) :=
      hfree.mono_right hin
    have holdfree : Disjoint F.surgery_times (Ioc b c) := by
      rw [Set.disjoint_left]
      intro z hz hzi
      exact Set.disjoint_left.mp hnewfree
        ((E.old_surgery_times z (hold ⟨hzi.1.le, hzi.2⟩)).mpr hz) hzi
    have hsb : a + s / q ∈ Icc b c := ⟨min_le_left _ _, le_max_left _ _⟩
    have htb : a + t / q ∈ Icc b c := ⟨min_le_right _ _, le_max_right _ _⟩
    rw [E.extended.slab_transport_coherent l r b c hlr hJ hfree hbc
      (hold.trans E.old_times) hnewfree _ _ hs' ht' hsb htb]
    rw [E.ordinary_compatibility b c hbc hold holdfree (hold.trans E.old_times)
      hnewfree ⟨_, hsb⟩ ⟨_, htb⟩]
    rw [d.slab_compatibility b c hbc hold holdfree s hs t ht hsb htb x hx]

end PoincareConjecture.SurgeryFlowExtension
