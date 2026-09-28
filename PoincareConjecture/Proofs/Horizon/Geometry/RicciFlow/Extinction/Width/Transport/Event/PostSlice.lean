import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Parent

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

noncomputable def m67WidthSliceCast {q : M59SphereQuotient}
    {U : GeneralizedSliceCarrier.{u}} {C C' : SurgerySelectedComponent U}
    (h : C' = C) (slice : M67WidthSlice q C) : M67WidthSlice q C' :=
  h.symm ▸ slice

theorem m67WidthSliceCast_heq {q : M59SphereQuotient}
    {U : GeneralizedSliceCarrier.{u}} {C C' : SurgerySelectedComponent U}
    (h : C' = C) (slice : M67WidthSlice q C) :
    HEq (m67WidthSliceCast h slice) slice := by
  subst C'
  rfl

theorem m67WidthSliceCast_alpha_heq {q : M59SphereQuotient}
    {U : GeneralizedSliceCarrier.{u}} {C C' : SurgerySelectedComponent U}
    (h : C' = C) (slice : M67WidthSlice q C) :
    HEq (m67WidthSliceCast h slice).alpha slice.alpha := by
  subst C'
  rfl

theorem m67WidthSliceCast_metric_heq {q : M59SphereQuotient}
    {U : GeneralizedSliceCarrier.{u}} {C C' : SurgerySelectedComponent U}
    (h : C' = C) (slice : M67WidthSlice q C) :
    HEq (m67WidthSliceCast h slice).metric slice.metric := by
  subst C'
  rfl

theorem m67WidthSliceCast_ambient_metric {q : M59SphereQuotient}
    {U : GeneralizedSliceCarrier.{u}} {C C' : SurgerySelectedComponent U}
    (h : C' = C) (slice : M67WidthSlice q C) :
    (m67WidthSliceCast h slice).ambient_metric = slice.ambient_metric := by
  subst C'
  rfl

theorem m67WidthSliceCast_basedWidth_eq {q : M59SphereQuotient}
    {U : GeneralizedSliceCarrier.{u}} {C C' : SurgerySelectedComponent U}
    (h : C' = C) (slice : M67WidthSlice q C) :
    m61BasedClassWidth q (m67WidthSliceCast h slice).metric C'.basepoint
        (m67WidthSliceCast h slice).alpha =
      m61BasedClassWidth q slice.metric C.basepoint slice.alpha := by
  subst C'
  rfl

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
  (H : RepairedAncestryTransportInput D W P K C)
  (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
  (hpost : Nonempty (D.flow.slice S.1).carrier)
  {q : M59SphereQuotient} (slice : M67WidthSlice q (P.component S))

noncomputable def m67EventPostSlice : M67WidthSlice q (H.event_input S hS hpost).child :=
  m67WidthSliceCast (eq_of_heq (H.event_child_path S hS hpost)) slice

theorem m67EventPostSlice_heq :
    HEq (m67EventPostSlice H S hS hpost slice) slice :=
  m67WidthSliceCast_heq _ _

theorem m67EventPostSlice_alpha_heq :
    HEq (m67EventPostSlice H S hS hpost slice).alpha slice.alpha :=
  m67WidthSliceCast_alpha_heq _ _

theorem m67EventPostSlice_metric_heq :
    HEq (m67EventPostSlice H S hS hpost slice).metric slice.metric :=
  m67WidthSliceCast_metric_heq _ _

theorem m67EventPostSlice_ambient_metric :
    (m67EventPostSlice H S hS hpost slice).ambient_metric = slice.ambient_metric :=
  m67WidthSliceCast_ambient_metric _ _

theorem m67EventPostSlice_based_width :
    m61BasedClassWidth q (m67EventPostSlice H S hS hpost slice).metric
        (H.event_input S hS hpost).child.basepoint
        (m67EventPostSlice H S hS hpost slice).alpha =
      m61BasedClassWidth q slice.metric (P.component S).basepoint slice.alpha :=
  m67WidthSliceCast_basedWidth_eq _ _

theorem m67EventPostSlice_metric
    (hambient : slice.ambient_metric = D.flow.metric S.1) :
    (m67EventPostSlice H S hS hpost slice).metric =
      (H.event_input S hS hpost).child_metric := by
  let post := m67EventPostSlice H S hS hpost slice
  have ha : post.ambient_metric = D.flow.metric S.1 :=
    (m67EventPostSlice_ambient_metric H S hS hpost slice).trans hambient
  have hi : post.metric.inner = (H.event_input S hS hpost).child_metric.inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [← post.metric_pullback, ha]
    exact (H.event_input S hS hpost).child_pullback x v w
  generalize post.metric = g at hi ⊢
  generalize (H.event_input S hS hpost).child_metric = g' at hi ⊢
  cases g
  cases g'
  cases hi
  rfl

end PoincareConjecture
