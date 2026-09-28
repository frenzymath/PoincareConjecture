import PoincareConjecture.Definitions.M71FiniteExtinction









set_option autoImplicit false

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}



noncomputable def m71InitialWidth (Q : M71FiniteContinuationService D W ancestry) : ℝ :=
  m61BasedClassWidth Q.identification_system.quotient Q.initial.metric
    ancestry.initial_component.basepoint Q.initial.alpha



theorem m71InitialWidth_nonneg (Q : M71FiniteContinuationService D W ancestry) :
    0 ≤ m71InitialWidth Q :=
  (Q.hM61.based_class Q.initial.metric ancestry.initial_component.compact
    ancestry.initial_component.connected ancestry.initial_component.basepoint
    Q.initial.pi_two_trivial Q.initial.alpha).nonnegative

end PoincareConjecture
