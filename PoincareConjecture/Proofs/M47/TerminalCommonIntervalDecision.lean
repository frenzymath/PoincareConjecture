import PoincareConjecture.Proofs.M47.TerminalCommonIntervalReindex
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal









set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47


theorem terminalCommonInterval_decide_countable (Ptest : ℕ → ℕ → Prop) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ j,
      (∀ᶠ k in atTop, Ptest j (sigma k)) ∨
      (∀ᶠ k in atTop, ¬ Ptest j (sigma k)) := by
  classical
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  let value (j k : ℕ) : Bool := decide (Ptest j k)
  obtain ⟨a, _, sigma, hsigma, hlim⟩ :=
    Poincare.exists_strictMono_tendsto_of_eventually_mem_isCompact
      value (fun _ => univ) (fun _ => isCompact_univ)
      (fun _ => Eventually.of_forall (fun _ => mem_univ _))
  refine ⟨sigma, hsigma, ?_⟩
  intro j
  have heq : ∀ᶠ k in atTop, value j (sigma k) = a j :=
    (hlim j).eventually ((isOpen_discrete ({a j} : Set Bool)).mem_nhds rfl)
  cases ha : a j with
  | false =>
    right
    filter_upwards [heq] with k hk
    exact of_decide_eq_false (by simpa only [value, ha] using hk)
  | true =>
    left
    filter_upwards [heq] with k hk
    exact of_decide_eq_true (by simpa only [value, ha] using hk)


theorem terminalCommonInterval_decide_encodable
    {ι : Type*} [Encodable ι] (Ptest : ι → ℕ → Prop) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ j,
      (∀ᶠ k in atTop, Ptest j (sigma k)) ∨
      (∀ᶠ k in atTop, ¬ Ptest j (sigma k)) := by
  let Q (n k : ℕ) := match Encodable.decode (α := ι) n with
    | some j => Ptest j k
    | none => True
  obtain ⟨sigma, hsigma, h⟩ := terminalCommonInterval_decide_countable Q
  refine ⟨sigma, hsigma, fun j => ?_⟩
  simpa only [Q, Encodable.encodek] using h (Encodable.encode j)


def TerminalCommonIntervalDecided (V : GeneralizedBlowupSequence.{u}) : Prop :=
  ∀ (q : ℚ) (b a m : ℕ),
    (∀ᶠ k in atTop, Nonempty
      (ControlledBlowupCylinder V k (a + 1) q b (1 / (m + 1)))) ∨
    (∀ᶠ k in atTop, ¬ Nonempty
      (ControlledBlowupCylinder V k (a + 1) q b (1 / (m + 1))))


theorem terminalCommonInterval_exists_decided (V : GeneralizedBlowupSequence.{u}) :
    ∃ sigma : ℕ → ℕ, ∃ hsigma : StrictMono sigma,
      TerminalCommonIntervalDecided (terminalCommonInterval_reindex V sigma hsigma) := by
  let Ptest (j : ℚ × ℕ × ℕ × ℕ) (k : ℕ) := Nonempty
    (ControlledBlowupCylinder V k (j.2.2.1 + 1) j.1 j.2.1 (1 / (j.2.2.2 + 1)))
  obtain ⟨sigma, hsigma, h⟩ := terminalCommonInterval_decide_encodable Ptest
  refine ⟨sigma, hsigma, fun q b a m => ?_⟩
  simpa only [terminalCommonInterval_reindex_cylinder_iff] using h (q, b, a, m)

end PoincareConjecture.M47
