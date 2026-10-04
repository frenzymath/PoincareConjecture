import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.DiameterLimit

/-!
# The terminal controlled-component alternative

Recurrent old-time controlled components through a positive regular worldline
give the actual terminal component, with the complete smooth topology and
strict sectional and intrinsic-diameter bounds at the doubled constant.
-/

noncomputable section

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

/-- The complete controlled-component certificate is constructed on the
actual terminal metric and its actual Levi-Civita connection. -/
def terminalCComponent (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    SingularCComponent (H.terminalMetric P04) (H.terminalConnection P04)
      (2 * H.constant) where
  constant_pos := mul_pos (by norm_num) H.constant_pos
  basepoint := x
  carrier := connectedComponent x
  component_eq := rfl
  compact := (H.terminal_topology_of_frequently_cComponent P04 x hfreq).1
  topology := (H.terminal_topology_of_frequently_cComponent P04 x hfreq).2
  positive_sectional y hy v w hvw :=
    (H.terminal_strict_sectional_bounds_of_frequently_cComponent P04 x hfreq hpos
      y hy v w hvw).1
  sectional_lower y hy v w hvw :=
    (H.terminal_strict_sectional_bounds_of_frequently_cComponent P04 x hfreq hpos
      y hy v w hvw).2
  diameter_lower :=
    (H.terminal_intrinsicDiameter_bounds_of_frequently_cComponent P04 x hfreq hpos).1
  diameter_upper :=
    (H.terminal_intrinsicDiameter_bounds_of_frequently_cComponent P04 x hfreq hpos).2

@[simp] theorem terminalCComponent_carrier (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    (H.terminalCComponent P04 x hfreq hpos).carrier = connectedComponent x := rfl

/-- The recurrent old-time component branch produces the exact doubled
terminal alternative containing the specified regular point. -/
theorem exists_terminal_cComponent_of_frequently
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ∃ N : SingularCComponent (H.terminalMetric P04) (H.terminalConnection P04)
        (2 * H.constant), N.basepoint = x ∧ N.carrier = connectedComponent x ∧ x ∈ N.carrier :=
  ⟨H.terminalCComponent P04 x hfreq hpos, rfl, rfl, mem_connectedComponent⟩

end PoincareMT.SingularTimeAssumptions
