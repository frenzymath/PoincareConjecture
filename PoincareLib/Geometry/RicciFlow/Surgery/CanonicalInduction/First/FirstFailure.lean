import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic
import Mathlib.Topology.Order.IsLUB

/-!
# Lemma 17.2: the first-failure infimum

Morgan--Tian Lemma 17.2, pp. 395-396. Failure on an observation gives a
nonempty bounded-below set of bad times, its finite infimum, canonical
control on the strict past, and an antitone bad-time sequence. These
statements do not yet assert that a bad point exists at the infimum.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.Proofs.M47

/-- The literal counterexample times in Morgan--Tian Lemma 17.2, p. 396,
with a high-scalar bad point on the actual slice at each such time. -/
def canonicalFailureTimes (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (r : ℝ) : Set ℝ :=
  {t | t ∈ surgeryObservationInterval O ∧
    ∃ x : (F.slice t).carrier,
      r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
      ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C}

/-- Observed canonical failure is precisely nonemptiness of the actual
counterexample-time set, Morgan--Tian Lemma 17.2, p. 396. -/
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

/-- Earlier canonical control puts every counterexample at or after its
endpoint, Morgan--Tian Lemma 17.2, first paragraph on p. 396. -/
theorem canonicalFailureTimes_lower_bound
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T0 r : ℝ}
    (hold : SurgeryCanonicalOn F (Ico 0 T0) r) :
    ∀ t ∈ canonicalFailureTimes F O r, T0 ≤ t := by
  rintro t ⟨ht, x, hscalar, hbad⟩
  apply le_of_not_gt
  intro hbefore
  exact hbad (hold t ⟨ht.1, hbefore⟩ (O.interval_subset ht) x hscalar)

/-- The minimizing bad-time sequence of Morgan--Tian Lemma 17.2, p. 396,
has a finite observed infimum with canonical strict past. Actual failure
at that infimum is the separate geometric attainment step. -/
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

end PoincareMT.Proofs.M47
