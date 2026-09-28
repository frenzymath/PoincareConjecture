import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

def canonicalFailureTimes (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (r : ℝ) : Set ℝ :=
  {t | t ∈ surgeryObservationInterval O ∧
    ∃ x : (F.slice t).carrier,
      r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
      ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C}

theorem canonicalFailureTimes_nonempty_iff
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) (r : ℝ) :
    (canonicalFailureTimes F O r).Nonempty ↔
      ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r := by
  constructor
  · rintro ⟨t, ht, x, hscalar, hbad⟩ hcanonical
    exact hbad (hcanonical t ht (O.interval_subset ht) x hscalar)
  · intro hfail
    by_contra hnone
    apply hfail
    intro t ht _ x hscalar
    by_contra hbad
    exact hnone ⟨t, ht, x, hscalar, hbad⟩

theorem canonicalFailureTimes_lower_bound
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T0 r : ℝ}
    (hold : SurgeryCanonicalOn F (Ico 0 T0) r) :
    ∀ t ∈ canonicalFailureTimes F O r, T0 ≤ t := by
  rintro t ⟨ht, x, hscalar, hbad⟩
  apply le_of_not_gt
  intro hbefore
  exact hbad (hold t ⟨ht.1, hbefore⟩ (O.interval_subset ht) x hscalar)

theorem exists_canonicalFailureInfimum
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T0 r : ℝ}
    (hT0 : 0 ≤ T0) (hold : SurgeryCanonicalOn F (Ico 0 T0) r)
    (hfail : ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r) :
    ∃ t ∈ Ico T0 O.H, t ∈ F.time_domain ∧
      SurgeryCanonicalOn F (Ico 0 t) r ∧
      ∃ times : ℕ → ℝ, Antitone times ∧ Tendsto times atTop (𝓝 t) ∧
        ∀ n, times n ∈ canonicalFailureTimes F O r := by
  have hnonempty := (canonicalFailureTimes_nonempty_iff F O r).mpr hfail
  have hbound := canonicalFailureTimes_lower_bound (O := O) hold
  have hbounded : BddBelow (canonicalFailureTimes F O r) := ⟨T0, hbound⟩
  have hlow : T0 ≤ sInf (canonicalFailureTimes F O r) := le_csInf hnonempty hbound
  obtain ⟨tbad, htbad⟩ := hnonempty
  have hhigh : sInf (canonicalFailureTimes F O r) < O.H :=
    (csInf_le hbounded htbad).trans_lt htbad.1.2
  refine ⟨sInf (canonicalFailureTimes F O r), ⟨hlow, hhigh⟩,
    O.interval_subset ⟨hT0.trans hlow, hhigh⟩, ?_, ?_⟩
  · intro t ht _ x hscalar
    by_contra hbad
    have hmem : t ∈ canonicalFailureTimes F O r :=
      ⟨⟨ht.1, ht.2.trans hhigh⟩, x, hscalar, hbad⟩
    exact (not_le_of_gt ht.2) (csInf_le hbounded hmem)
  · exact exists_seq_tendsto_sInf ⟨tbad, htbad⟩ hbounded

end PoincareConjecture.Proofs.M47
