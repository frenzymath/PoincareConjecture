import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Slice.Family
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.PostSlice

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
  {H : RepairedAncestryTransportInput D W P K C}
  {B : M59HigherBasepointTransportService.{u}}
  {A : RepairedAncestryTransportData D W P K C H B}
  {Syst : M59IdentificationSystem.{u}}
  {initial : M67InitialClassData Syst (P.component (m67InitialTime P)) (D.flow.metric 0)}

theorem M67ClassPath.slice_alpha
    (X : M67ClassPath H B A Syst initial) (s : Set.Icc (0 : ℝ) T) :
    (m67SliceFamily Syst initial X.datum s).alpha = (X.datum s).alpha :=
  m67SliceFamily_alpha Syst initial X.datum
    (congrArg M67ClassDatum.alpha X.initial_eq) s

theorem m67_class_path_event_family_exists
    (X : M67ClassPath H B A Syst initial)
    (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (hdelta : D.flow.parameters.delta S.1 < repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h S.1 < repairedComparisonHeightBound D.flow.local_constants)
    (eta : ℝ) (heta : 0 < eta)
    (post : M67WidthSlice Syst.quotient (H.event_input S hS hpost).child)
    (hpostmetric : post.metric = (H.event_input S hS hpost).child_metric)
    (hpostalpha : HEq post.alpha (m67SliceFamily Syst initial X.datum S).alpha) :
    Nonempty {F : M67EventTransportFamily B A Syst.quotient S hS hpost hdelta hh eta heta //
      ∀ s hnear hbefore hafter hJ,
        (F.transport s hnear hbefore hafter hJ).pre = m67SliceFamily Syst initial X.datum s ∧
        (F.transport s hnear hbefore hafter hJ).post = post} := by
  apply m67_event_transport_family_exists B A Syst S hS hpost hdelta hh eta heta
    (m67SliceFamily Syst initial X.datum)
    (m67SliceFamily_ambient_metric Syst initial X.datum) post hpostmetric
  intro s hs _hsS hJ f hsmooth hbase hmap
  have hpostclass : post.alpha = (m67EventPostClassDatum H B A Syst S hS hpost hdelta hh
      (X.datum (m67EventPreTime S hS hpost))).alpha :=
    eq_of_heq ((hpostalpha.trans (heq_of_eq (X.slice_alpha S))).trans
      (X.event_post_alpha_heq S hS hpost hdelta hh).symm)
  rw [X.slice_alpha s, hpostclass]
  exact X.event_approximant_transport S hS hpost hdelta hh s hs hJ f hsmooth hbase hmap

theorem m67_class_path_actual_event_family_exists
    (X : M67ClassPath H B A Syst initial)
    (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (hdelta : D.flow.parameters.delta S.1 < repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h S.1 < repairedComparisonHeightBound D.flow.local_constants)
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty {F : M67EventTransportFamily B A Syst.quotient S hS hpost hdelta hh eta heta //
      ∀ s hnear hbefore hafter hJ,
        (F.transport s hnear hbefore hafter hJ).pre = m67SliceFamily Syst initial X.datum s ∧
        (F.transport s hnear hbefore hafter hJ).post =
          m67EventPostSlice H S hS hpost (m67SliceFamily Syst initial X.datum S)} :=
  m67_class_path_event_family_exists X S hS hpost hdelta hh eta heta
    (m67EventPostSlice H S hS hpost (m67SliceFamily Syst initial X.datum S))
    (m67EventPostSlice_metric H S hS hpost (m67SliceFamily Syst initial X.datum S)
      (m67SliceFamily_ambient_metric Syst initial X.datum S))
    (m67EventPostSlice_alpha_heq H S hS hpost (m67SliceFamily Syst initial X.datum S))

noncomputable def m67ClassPathEventFamily
    (X : M67ClassPath H B A Syst initial)
    (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (hdelta : D.flow.parameters.delta S.1 < repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h S.1 < repairedComparisonHeightBound D.flow.local_constants)
    (eta : ℝ) (heta : 0 < eta) :
    M67EventTransportFamily B A Syst.quotient S hS hpost hdelta hh eta heta :=
  (Classical.choice (m67_class_path_actual_event_family_exists X S hS hpost hdelta hh eta heta)).val

theorem m67ClassPathEventFamily_slices
    (X : M67ClassPath H B A Syst initial)
    (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (hdelta : D.flow.parameters.delta S.1 < repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h S.1 < repairedComparisonHeightBound D.flow.local_constants)
    (eta : ℝ) (heta : 0 < eta)
    (s : Set.Icc (0 : ℝ) T)
    (hnear : S.1 - (m67ClassPathEventFamily X S hS hpost hdelta hh eta heta).delta < s.1)
    (hbefore : s.1 < S.1)
    (hafter : (D.flow.event S.1 hS).tMinus < s.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1)) :
    let E := (m67ClassPathEventFamily X S hS hpost hdelta hh eta heta).transport
      s hnear hbefore hafter hJ
    E.pre = m67SliceFamily Syst initial X.datum s ∧
      E.post = m67EventPostSlice H S hS hpost (m67SliceFamily Syst initial X.datum S) :=
  (Classical.choice (m67_class_path_actual_event_family_exists X S hS hpost hdelta hh eta heta)).property
    s hnear hbefore hafter hJ

end PoincareConjecture
