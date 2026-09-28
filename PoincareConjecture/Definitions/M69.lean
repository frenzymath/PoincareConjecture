import PoincareConjecture.Definitions.M68
import PoincareConjecture.Statements.M67
import PoincareConjecture.Statements.M61Width
import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Definitions.M57Transport
















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

abbrev M69AlphaTransport := @M67AlphaTransport

structure M69ClassLedger
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    (B : M59HigherBasepointTransportService)
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65) where

  alpha : ∀ s : Set.Icc (0 : ℝ) T,
    HomotopyGroup.Pi 2
      (C1FreeLoopSpace (M := (P.component s).carrier.carrier))
      (constantC1Loop (P.component s).basepoint)
  alpha_eq_slice : ∀ s, alpha s = (X.slice s).alpha
  initial_nonzero :
    (X.slice ⟨0, ⟨le_rfl, X.terminal_nonnegative⟩⟩).loop_pi_three
        (alpha ⟨0, ⟨le_rfl, X.terminal_nonnegative⟩⟩) ≠ 1
  regular_transport : ∀ {a b : ℝ}
      (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b)),
      M69AlphaTransport B
      (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).basepoint
        (P.component ⟨b, ⟨ha.trans hab.le, hb⟩⟩).basepoint
        (repairedDiffeomorphContinuousMap
          (P.regular_transport
            ⟨a, ⟨ha, hab.le.trans hb⟩⟩
            ⟨b, ⟨ha.trans hab.le, hb⟩⟩ hab hJ))
        (alpha ⟨a, ⟨ha, hab.le.trans hb⟩⟩)
        (alpha ⟨b, ⟨ha.trans hab.le, hb⟩⟩)


  event_transport : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
      ∀ hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      ∀ (eta : ℝ) (heta : 0 < eta),
      ∀ s : Set.Icc (0 : ℝ) T,
        ∀ hnear : S.1 - (X.event_transport S hS hpost hdelta hh eta heta).delta < s.1,
        ∀ hbefore : s.1 < S.1,
        ∀ hafter : (D.flow.event S.1 hS).tMinus < s.1,
        ∀ hJ : Disjoint D.flow.surgery_times
          (Set.Ioc (D.flow.event S.1 hS).tMinus s.1),
        let E := (X.event_transport S hS hpost hdelta hh eta heta).transport
          s hnear hbefore hafter hJ
        And (HEq E.pre.alpha (alpha s))
          (And (HEq E.post.alpha (alpha S))
            (M59HigherBasepointTransport.map
              (B.transport 2) E.loop_basepoint_path.loop
              (surgeryHomotopyMap (n := 2) E.loop.map
                (E.loop.map_based (rfl :
                  E.f (P.component s).basepoint =
                    E.f (P.component s).basepoint)) E.pre.alpha) =
                E.post.alpha))




noncomputable def m69M67Choice
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    (hcomparison : M67EventComparisonBounds D.flow (Set.Icc 0 T))
    (hscalar : M67ScalarLowerBound D.flow (Set.Icc 0 T))
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K)
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (hM61 : M61WidthTheory.{u} S.quotient)
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hM67 : M67SurgeryWidthTheory.{u}) :
    {X : M67ChangingWidthPath D W P K C H B A S.quotient
        hM61.toM61RawWidthCore hM65 //
      M67AnchoredConclusion S initial X} :=
  Classical.choice
    (hM67 D W P hcomparison hscalar K C H B A S initial hM61 hM65 hM58 hM66)

structure M69FinitePieceInput
    {g₀ : StandardInitialMetric}
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
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (L : M69ClassLedger P B X) where
  T₁ : ℝ
  T₂ : ℝ
  ordered : 0 ≤ T₁ ∧ T₁ ≤ T₂ ∧ T₂ ≤ T
  chronology : M67FiniteChronology
    (↑P.surgery_times : Set ℝ) T₁ T₂



  start_width_properties :
    M61BasedClassWidthProperties q
      (X.slice ⟨T₁, ⟨ordered.1, ordered.2.1.trans ordered.2.2⟩⟩).metric
      (P.component ⟨T₁, ⟨ordered.1, ordered.2.1.trans ordered.2.2⟩⟩).basepoint
      (X.slice ⟨T₁, ⟨ordered.1, ordered.2.1.trans ordered.2.2⟩⟩).alpha
  initial_width_properties :
    M61BasedClassWidthProperties q
      (X.slice ⟨0, ⟨le_rfl, X.terminal_nonnegative⟩⟩).metric
      (P.component ⟨0, ⟨le_rfl, X.terminal_nonnegative⟩⟩).basepoint
      (X.slice ⟨0, ⟨le_rfl, X.terminal_nonnegative⟩⟩).alpha

def M69FinitePieceInput.profile
    {g₀ : StandardInitialMetric}
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
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    (L : M69ClassLedger P B X)
    (I : M69FinitePieceInput X L)
    (HX : M67Conclusion X) : M68ProfileInput X HX :=
  { T₁ := I.T₁
    T₂ := I.T₂
    ordered := I.ordered
    chronology := I.chronology }

structure M69FinitePieceConclusion
    {g₀ : StandardInitialMetric}
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
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    (L : M69ClassLedger P B X) (I : M69FinitePieceInput X L)
    (HX : M67Conclusion X) where
  profile : M68ProfileConclusion (M69FinitePieceInput.profile L I HX)
  initial_width_eq :
    X.width (M68ProfileInput.start (M69FinitePieceInput.profile L I HX)) =
      m61FreeClassWidth
        (X.slice (M68ProfileInput.start (M69FinitePieceInput.profile L I HX))).metric
        (X.slice (M68ProfileInput.start (M69FinitePieceInput.profile L I HX))).family
  transported_class_nonzero : ∀ s : Set.Icc (0 : ℝ) T,
    (X.slice s).loop_pi_three (L.alpha s) ≠ 1

end PoincareConjecture
