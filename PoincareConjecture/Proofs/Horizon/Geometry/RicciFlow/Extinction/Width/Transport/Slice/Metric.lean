import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.SliceBuilder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.ComponentRestriction
import PoincareConjecture.Definitions.M67InitialClass

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

noncomputable def m67InitialWidthSlice
    (S : M59IdentificationSystem.{u})
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier)
    (initial : M67InitialClassData S C g) : M67WidthSlice S.quotient C :=
  m67WidthSliceOfClass S C g initial.metric initial.metric.leviCivitaData
    initial.metric_pullback initial.pi_two_trivial initial.alpha initial.nonzero

noncomputable def m67ActualWidthSlice
    (S : M59IdentificationSystem.{u})
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint))
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
      (constantC1Loop C.basepoint))
    (hnonzero : (S.core C.compact C.connected C.basepoint hpi).pi_two_pi_three
      alpha ≠ 1) : M67WidthSlice S.quotient C :=
  let gC := g.pullbackOfLocalDiffeomorph C.inclusion
    (selectedComponentInclusionLocalDiffeomorph C)
  m67WidthSliceOfClass S C g gC gC.leviCivitaData (fun _ _ _ => rfl)
    hpi alpha hnonzero

theorem M67WidthSlice.scalarCurvature_eq_ambient
    {q : M59SphereQuotient}
    {A : GeneralizedSliceCarrier.{u}} {C : SurgerySelectedComponent A}
    (slice : M67WidthSlice q C) (D : LeviCivitaData slice.ambient_metric)
    (x : C.carrier.carrier) :
    slice.connection.scalarCurvature x = D.scalarCurvature (C.inclusion x) := by
  exact slice.connection.scalarCurvature_eq_of_local_isometry D
    isOpen_univ C.inclusion_smooth.contMDiffOn
    (fun y _ v w => (slice.metric_pullback y v w).symm) (Set.mem_univ x)

theorem M67WidthSlice.scalar_infimum_lower_bound
    {q : M59SphereQuotient}
    {A : GeneralizedSliceCarrier.{u}} {C : SurgerySelectedComponent A}
    (slice : M67WidthSlice q C) (D : LeviCivitaData slice.ambient_metric)
    {r : ℝ} (hr : ∀ x : A.carrier, r ≤ D.scalarCurvature x) :
    r ≤ sInf (Set.range slice.connection.scalarCurvature) := by
  have hne : (Set.range slice.connection.scalarCurvature).Nonempty :=
    ⟨_, C.basepoint, rfl⟩
  apply le_csInf hne
  rintro _ ⟨x, rfl⟩
  rw [slice.scalarCurvature_eq_ambient D x]
  exact hr _

end PoincareConjecture
