import PoincareConjecture.Definitions.M71FiniteExtinction
import PoincareConjecture.Proofs.M67.InitialClass
import PoincareConjecture.Proofs.M69.Inputs

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def m71InitialClassAlongEq
    {F : GeneralizedSliceCarrier.{u}} (g : RiemannianMetric 3 F.carrier)
    (S : M59IdentificationSystem.{u}) {C C₀ : SurgerySelectedComponent F}
    (h : C = C₀) (initial : M67InitialClassData S C₀ g) :
    M67InitialClassData S C g := h.symm ▸ initial

theorem m71InitialClassAlongEq_width
    {F : GeneralizedSliceCarrier.{u}} (g : RiemannianMetric 3 F.carrier)
    (S : M59IdentificationSystem.{u}) {C C₀ : SurgerySelectedComponent F}
    (h : C = C₀) (initial : M67InitialClassData S C₀ g) :
    m61BasedClassWidth S.quotient (m71InitialClassAlongEq g S h initial).metric
        C.basepoint (m71InitialClassAlongEq g S h initial).alpha =
      m61BasedClassWidth S.quotient initial.metric C₀.basepoint initial.alpha := by
  cases h
  rfl

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}
  (Q : M71FiniteContinuationService D W ancestry)
  {T : ℝ} {hT : T ∈ D.flow.time_domain}
  (J : M71ComponentContinuationData D W ancestry Q.basepoint_service T hT)
  (hM67 : M67SurgeryWidthTheory.{u})

noncomputable def m71WidthChoice :=
  m69M67Choice W J.P
    (fun t _ ht => Q.comparison_bounds t (Set.mem_univ t) ht)
    (fun t _ ht => Q.scalar_lower_bound t (Set.mem_univ t) ht)
    J.K J.C J.H Q.basepoint_service J.A
    Q.identification_system
    (m71InitialClassAlongEq (D.flow.metric 0) Q.identification_system
      (ancestry.path_for_initial T hT J.terminal_point) Q.initial)
    Q.hM61 Q.hM65 Q.hM58 Q.hM66 hM67

noncomputable def m71ClassLedger :=
  m69ClassLedgerFromM67 (m71WidthChoice Q J hM67).1 (m71WidthChoice Q J hM67).2

noncomputable def m71ComparisonInterval :=
  m69FullIntervalInput Q.hM61 (m71WidthChoice Q J hM67).1 (m71ClassLedger Q J hM67)

theorem m71WidthChoice_initial_width :
    (m71WidthChoice Q J hM67).1.width (m67InitialTime J.P) =
      m61BasedClassWidth Q.identification_system.quotient Q.initial.metric
        ancestry.initial_component.basepoint Q.initial.alpha := by
  exact (m67AnchoredInitialWidth (m71WidthChoice Q J hM67).2).trans
    (m71InitialClassAlongEq_width (D.flow.metric 0) Q.identification_system
      (ancestry.path_for_initial T hT J.terminal_point) Q.initial)

@[simp] theorem m71ComparisonInterval_start :
    (m71ComparisonInterval Q J hM67).T₁ = 0 := rfl

@[simp] theorem m71ComparisonInterval_end :
    (m71ComparisonInterval Q J hM67).T₂ = T := rfl

theorem m71FinitePieceApplication
    (hM68 : M68ScalarClockStatement.{u}) (hM69 : M69FinitePieceStatement.{u}) :
    Nonempty (M69FinitePieceConclusion (m71ClassLedger Q J hM67)
      (m71ComparisonInterval Q J hM67) (m71WidthChoice Q J hM67).2.estimate) := by
  obtain ⟨C, _hprofile⟩ := hM69
    (fun t _ ht => Q.comparison_bounds t (Set.mem_univ t) ht)
    (fun t _ ht => Q.scalar_lower_bound t (Set.mem_univ t) ht)
    Q.identification_system
    (m71InitialClassAlongEq (D.flow.metric 0) Q.identification_system
      (ancestry.path_for_initial T hT J.terminal_point) Q.initial)
    Q.hM58 Q.hM66 hM67 hM68
    (m71ClassLedger Q J hM67) (m71ComparisonInterval Q J hM67)
  exact ⟨C⟩

end PoincareConjecture
