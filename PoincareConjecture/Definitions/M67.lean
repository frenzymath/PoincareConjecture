import PoincareConjecture.Definitions.M57Transport
import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Definitions.M61Width
import PoincareConjecture.Definitions.M66

















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



def M67EventComparisonBounds (F : SurgeryFlowData.{u}) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, t ∈ F.surgery_times →
    F.parameters.delta t < repairedComparisonDeltaBound F.local_constants ∧
      F.parameters.h t < repairedComparisonHeightBound F.local_constants



def M67ScalarLowerBound (F : SurgeryFlowData.{u}) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
    -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x



def M67AlphaTransport {M N : Type u}
    [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace LoopAmbient N]
    [IsManifold (𝓡 3) ∞ N]
    (B : M59HigherBasepointTransportService)
    (x : M) (y : N)
    (f : ContinuousMap M N)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x))
    (beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N))
      (constantC1Loop y)) : Prop :=
  ∃ L : M59LoopPostcomposition f,
    ∃ p : Path (f x) y,
      ∃ lp : M59ConstantLoopPath p,
        M59HigherBasepointTransport.map (B.transport 2) lp.loop
          (surgeryHomotopyMap (n := 2) L.map
            (L.map_based (rfl : f x = f x)) alpha) = beta


structure M67WidthSlice (q : M59SphereQuotient)
    {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A) where
  ambient_metric : RiemannianMetric 3 A.carrier
  metric : RiemannianMetric 3 C.carrier.carrier
  connection : LeviCivitaData metric
  metric_pullback : ∀ x v w,
    ambient_metric.inner (C.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = metric.inner x v w
  family : ContinuousMap LoopTwoSphere
    (C1FreeLoopSpace (M := C.carrier.carrier))
  family_null : M61NullFamily family
  alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
    (constantC1Loop C.basepoint)
  represents : M61Represents q C.basepoint alpha family
  pi_two_trivial : Subsingleton
    (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint)
  loop_pi_three : HomotopyGroup.Pi 2
      (C1FreeLoopSpace (M := C.carrier.carrier))
      (constantC1Loop C.basepoint) ≃*
        HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint
  class_nonzero : loop_pi_three alpha ≠ 1


structure M67FiniteChronology (events : Set ℝ) (a b : ℝ) where
  count : ℕ
  time : Fin count → ℝ
  strict_mono : StrictMono time
  in_interval : ∀ i, time i ∈ Set.Ioo a b
  complete : Set.range time = events ∩ Set.Ioo a b


structure M67EventTransport
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (q : M59SphereQuotient)
    (S : Set.Icc (0 : ℝ) T)
    (s : Set.Icc (0 : ℝ) T)
    (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (hdelta : D.flow.parameters.delta S.1 <
      repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h S.1 <
      repairedComparisonHeightBound D.flow.local_constants)
    (eta : ℝ) (heta : 0 < eta) where


  pre : M67WidthSlice q (P.component s)
  post : M67WidthSlice q (H.event_input S hS hpost).child
  pretime_lt : (D.flow.event S.1 hS).tMinus < s.1
  pre_no_surgery : Disjoint D.flow.surgery_times
    (Set.Ioc (D.flow.event S.1 hS).tMinus s.1)
  parent_identification : Diffeomorph (𝓡 3) (𝓡 3)
    (P.component ⟨(D.flow.event S.1 hS).tMinus,
      ⟨(D.flow.event S.1 hS).tMinus_nonnegative,
        (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩⟩).carrier.carrier
    (H.event_input S hS hpost).parent.carrier.carrier ∞
  parent_identification_eq : ∀ x,
    (H.event_input S hS hpost).parent.inclusion
      (parent_identification x) =
      (P.component ⟨(D.flow.event S.1 hS).tMinus,
        ⟨(D.flow.event S.1 hS).tMinus_nonnegative,
          (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩⟩).inclusion x
  parent_identification_based :
    Path
      (parent_identification
        (P.component ⟨(D.flow.event S.1 hS).tMinus,
          ⟨(D.flow.event S.1 hS).tMinus_nonnegative,
            (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩⟩).basepoint)
      (H.event_input S hS hpost).parent.basepoint
  pre_to_parent : Diffeomorph (𝓡 3) (𝓡 3)
    (P.component s).carrier.carrier
    (H.event_input S hS hpost).parent.carrier.carrier ∞
  pre_to_parent_eq_regular : ∀ x,
    pre_to_parent x = parent_identification
      ((P.regular_transport
        ⟨(D.flow.event S.1 hS).tMinus,
          ⟨(D.flow.event S.1 hS).tMinus_nonnegative,
            (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩⟩
        s pretime_lt pre_no_surgery).symm x)
  pre_metric_eq_parent : ∀ x v w,
    ((H.event_input S hS hpost).parent_metric s.1).inner
      (pre_to_parent x)
      (mfderiv (𝓡 3) (𝓡 3) pre_to_parent x v)
      (mfderiv (𝓡 3) (𝓡 3) pre_to_parent x w) =
      pre.metric.inner x v w
  f : ContinuousMap
    (P.component s).carrier.carrier
    (H.event_input S hS hpost).child.carrier.carrier
  smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f
  based_path : Path (f (P.component s).basepoint)
    (H.event_input S hS hpost).child.basepoint
  loop_basepoint_path : M59ConstantLoopPath based_path
  loop : M59LoopPostcomposition f
  class_transport :
    M59HigherBasepointTransport.map (B.transport 2) loop_basepoint_path.loop
      (surgeryHomotopyMap (n := 2) loop.map
        (loop.map_based (rfl : f (P.component s).basepoint =
          f (P.component s).basepoint)) pre.alpha) = post.alpha
  null_transport : ∀ γ, IsNullHomotopicLoop γ →
    IsNullHomotopicLoop (loop.map γ)



  comparison_homotopy :
    ContinuousMap.Homotopic f
      ((A.event_output S hS hpost hdelta hh).comparison.map.comp
        (repairedDiffeomorphContinuousMap pre_to_parent))
  child_metric_eq : post.metric =
    (H.event_input S hS hpost).child_metric
  distance_bound : ∀ x y,
    post.metric.edist (f x) (f y) ≤
      ENNReal.ofReal (1 + eta) * pre.metric.edist x y


  filling_transport : ∀ γ (Dγ : LipschitzSpanningDisk pre.metric γ),
    ∃ Eγ : LipschitzSpanningDisk post.metric (loop.map γ),
      Eγ.area ≤ (1 + eta) ^ 2 * Dγ.area








  represents_transport : ∀ F : ContinuousMap LoopTwoSphere
      (C1FreeLoopSpace (M := (P.component s).carrier.carrier)),
    M61NullFamily F →
    M61Represents q (P.component s).basepoint pre.alpha F →
      M61Represents q (H.event_input S hS hpost).child.basepoint post.alpha
        (loop.map.comp F)

structure M67EventTransportFamily
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (q : M59SphereQuotient)
    (S : Set.Icc (0 : ℝ) T)
    (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (hdelta : D.flow.parameters.delta S.1 <
      repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h S.1 <
      repairedComparisonHeightBound D.flow.local_constants)
    (eta : ℝ) (heta : 0 < eta) where
  delta : ℝ
  delta_pos : 0 < delta
  transport : ∀ s : Set.Icc (0 : ℝ) T,
    S.1 - delta < s.1 → s.1 < S.1 →
    (D.flow.event S.1 hS).tMinus < s.1 →
    Disjoint D.flow.surgery_times
      (Set.Ioc (D.flow.event S.1 hS).tMinus s.1) →
    M67EventTransport B A q S s hS hpost hdelta hh eta heta

end PoincareConjecture
