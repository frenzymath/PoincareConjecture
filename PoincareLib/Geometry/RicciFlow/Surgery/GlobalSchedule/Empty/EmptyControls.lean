import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyExtension
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionNoncollapse

/-!
# Geometric controls on the permanent empty extension

Morgan--Tian Section 17.2, p. 409. The original controls apply at every
nonempty slice, whose physical time precedes the empty cutoff. Later slices
have no spatial points. The supplied scale-one M13 calculus transports the
actual old canonical neighborhoods and tested noncollapse cylinders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

/-- The absolute-time pinching inequalities retain their original clock. -/
theorem pinched (h : SurgeryFlowPinched F) : SurgeryFlowPinched (flow F ha) := by
  intro t ht
  by_cases hta : t ≤ a
  · have htold : t ∈ F.time_domain :=
      F.time_domain_interval.out F.zero_mem ha ⟨ht, hta⟩
    change SurgeryPinchedAt (F.connection (min t a)) t
    rw [min_eq_left hta]
    exact h t htold
  · let : IsEmpty ((flow F ha).slice t).carrier :=
      flow_empty_after F ha (lt_of_not_ge hta).le
    refine ⟨ht, ?_, ?_⟩
    · intro x
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x

/-- Every actual point uses the old canonical control with the same r,
epsilon and C. The singleton window does not alter the parameter profiles. -/
theorem canonical (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (h : SurgeryCanonicalAssumption F) : SurgeryCanonicalAssumption (flow F ha) := by
  intro t ht x
  let : Nonempty (slice F a t).carrier := ⟨x⟩
  have hta : t < a := time_lt_of_nonempty F a
  have htold : t ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem ha ⟨ht, hta.le⟩
  have hJ : ({t} : Set ℝ) ⊆ F.time_domain := by
    intro s hs
    have hs' : s = t := mem_singleton_iff.mp hs
    subst s
    exact htold
  have hold : SurgeryCanonicalOn F {t} (F.parameters.r t) := by
    intro s hs hsold
    have hs' : s = t := mem_singleton_iff.mp hs
    subst s
    exact h t hsold
  exact (extension F ha).canonical_on m13 hJ hold t (mem_singleton t) ht x

/-- Pull each tested cylinder back to the old flow, preserving its radius,
kappa, terminal ball and positive-component exception. -/
theorem noncollapsed (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (h : SurgeryNoncollapsed F) : SurgeryNoncollapsed (flow F ha) := by
  intro t ht x
  let : Nonempty (slice F a t).carrier := ⟨x⟩
  have hta : t < a := time_lt_of_nonempty F a
  have htold : t ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem ha ⟨ht, hta.le⟩
  have hJ : ({t} : Set ℝ) ⊆ F.time_domain := by
    intro s hs
    have hs' : s = t := mem_singleton_iff.mp hs
    subst s
    exact htold
  have hold : SurgeryNoncollapsedOn F {t} (F.parameters.kappa t) := by
    intro s hs hsold
    have hs' : s = t := mem_singleton_iff.mp hs
    subst s
    exact h t hsold
  exact (extension F ha).noncollapsed_on m13 hJ hold t (mem_singleton t) ht x

end PoincareMT.M51Empty
