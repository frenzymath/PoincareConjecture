import PoincareLib.Geometry.RicciFlow.Extinction.Width.Path.Data
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.IdentificationTheory

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Build one metric-calibrated width slice from a nonzero loop-space class.
The M59 core supplies the normalized regular family and the canonical
loop-space-to-`pi₃` identification; chronology is deliberately outside this
pointwise constructor. -/
noncomputable def m67WidthSliceOfClass
    (S : M59IdentificationSystem.{u})
    {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A)
    (ambient_metric : RiemannianMetric 3 A.carrier)
    (metric : RiemannianMetric 3 C.carrier.carrier)
    (connection : LeviCivitaData metric)
    (metric_pullback : ∀ x v w,
      ambient_metric.inner (C.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = metric.inner x v w)
    (pi_two_trivial : Subsingleton
      (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint))
    (alpha : HomotopyGroup.Pi 2
      (C1FreeLoopSpace (M := C.carrier.carrier))
      (constantC1Loop C.basepoint))
    (hα : (S.core C.compact C.connected C.basepoint pi_two_trivial).pi_two_pi_three
      alpha ≠ 1) :
    M67WidthSlice S.quotient C := by
  let core := S.core C.compact C.connected C.basepoint pi_two_trivial
  let hrep := core.regular_representatives alpha
  let Gamma := Classical.choose hrep
  have hGamma := Classical.choose_spec hrep
  refine
    { ambient_metric := ambient_metric
      metric := metric
      connection := connection
      metric_pullback := metric_pullback
      family := m59FamilyMap Gamma
      family_null := fun c => Gamma.null_homotopic c
      alpha := alpha
      represents := ⟨Gamma, hGamma.1, hGamma.2, by rfl⟩
      pi_two_trivial := pi_two_trivial
      loop_pi_three := core.pi_two_pi_three
      class_nonzero := hα }

end PoincareMT
