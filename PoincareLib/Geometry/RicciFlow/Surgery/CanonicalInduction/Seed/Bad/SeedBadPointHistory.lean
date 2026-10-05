import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceFrontier

/-!
# The physical first-failure point has a selected-history preimage

At a nonsurgery time the M33 regular image is the whole slice. At a
surgery time the finite cap frontier supplies a cap whenever the point
is outside the selected history image; a separately produced canonical
control on every such cap then contradicts the failure predicate.
Claim 17.9, pp. 405-407; blowup-source-raw-birth-canonical.md.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M47

/-- A physical point that fails canonical control is in the selected
regular history whenever every cap containing it is controlled. -/
theorem exists_first_failure_history_preimage
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base : ℝ}
    (ht : base ∈ H.generalized.interval)
    (x : (F.slice base).carrier)
    (hfail : ¬ SurgeryCanonicalControl F base x F.parameters.epsilon F.parameters.C)
    (hcap : ∀ (hT : base ∈ F.surgery_times),
      ∀ [Nonempty (F.slice base).carrier],
      ∀ (i : Fin (F.event base hT).cap_count),
        x ∈ ((F.event base hT).caps i).carrier →
          SurgeryCanonicalControl F base x F.parameters.epsilon F.parameters.C) :
    ∃ y : (H.generalized.slice base).carrier,
      H.history.forward base ht y = x := by
  classical
  by_cases hT : base ∈ F.surgery_times
  · let inst : Nonempty (F.slice base).carrier := ⟨x⟩
    by_cases hx : x ∈ Set.range (H.history.forward base ht)
    · exact hx
    · obtain ⟨i, hxi⟩ := @cap_contact_of_not_regular_history F W H base ht hT inst x hx
      exact False.elim (hfail (@hcap hT inst i hxi))
  · have hxreg : x ∈ m33RegularRegion F base := by
      rw [m33RegularRegion_of_regular F base hT]
      exact mem_univ x
    rw [← H.regular_range base ht] at hxreg
    exact hxreg

end PoincareMT.M47
