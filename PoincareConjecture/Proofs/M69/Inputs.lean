import PoincareConjecture.Definitions.M69

set_option autoImplicit false

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric}
  {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {T : ℝ} {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D}
  {C : RepairedComparisonHomotopyData D K}
  {H : RepairedAncestryTransportInput D W P K C}
  {B : M59HigherBasepointTransportService}
  {A : RepairedAncestryTransportData D W P K C H B}
  {q : M59SphereQuotient}
  {hM61 : M61RawWidthCore.{u}}
  {hM64 : M64ComparisonTheory.{u}}
  {hM65 : M65DeformationTheory hM61 hM64}

def m69ClassLedgerFromCoherence
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (coherent : M67ClassCoherence X) : M69ClassLedger P B X where
  alpha := fun s => (X.slice s).alpha
  alpha_eq_slice := fun _ => rfl
  initial_nonzero := (X.slice (m67InitialTime P)).class_nonzero
  regular_transport := coherent.regular_transport
  event_transport := coherent.event_transport

def m69ClassLedgerFromM67
    {S : M59IdentificationSystem.{u}}
    {initial : M67InitialClassData S
      (P.component (m67InitialTime P)) (D.flow.metric 0)}
    (X : M67ChangingWidthPath D W P K C H B A S.quotient hM61 hM65)
    (anchored : M67AnchoredConclusion S initial X) : M69ClassLedger P B X :=
  m69ClassLedgerFromCoherence X anchored.class_coherence

def m69FullIntervalInput
    (hWidth : M61WidthTheory.{u} q)
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (L : M69ClassLedger P B X) : M69FinitePieceInput X L where
  T₁ := 0
  T₂ := T
  ordered := ⟨le_rfl, X.terminal_nonnegative, le_rfl⟩
  chronology := X.chronology
  start_width_properties := hWidth.based_class
    (X.slice (m67InitialTime P)).metric
    (P.component (m67InitialTime P)).compact
    (P.component (m67InitialTime P)).connected
    (P.component (m67InitialTime P)).basepoint
    (X.slice (m67InitialTime P)).pi_two_trivial
    (X.slice (m67InitialTime P)).alpha
  initial_width_properties := hWidth.based_class
    (X.slice (m67InitialTime P)).metric
    (P.component (m67InitialTime P)).compact
    (P.component (m67InitialTime P)).connected
    (P.component (m67InitialTime P)).basepoint
    (X.slice (m67InitialTime P)).pi_two_trivial
    (X.slice (m67InitialTime P)).alpha

@[simp] theorem m69FullIntervalInput_start
    (hWidth : M61WidthTheory.{u} q)
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (L : M69ClassLedger P B X) : (m69FullIntervalInput hWidth X L).T₁ = 0 := rfl

@[simp] theorem m69FullIntervalInput_end
    (hWidth : M61WidthTheory.{u} q)
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (L : M69ClassLedger P B X) : (m69FullIntervalInput hWidth X L).T₂ = T := rfl

end PoincareConjecture
