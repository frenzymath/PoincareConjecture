import PoincareConjecture.Statements.M67
import PoincareConjecture.Statements.Ch01.Topology










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m67AnchoredInitialWidth
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B₀ : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B₀}
    {S : M59IdentificationSystem.{u}}
    {hM61 : M61RawWidthCore.{u}} {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0)}
    {X : M67ChangingWidthPath D W P K C H B₀ A S.quotient hM61 hM65}
    (B : M67AnchoredConclusion S initial X) :
    X.width (m67InitialTime P) =
      m61BasedClassWidth S.quotient initial.metric
        (P.component (m67InitialTime P)).basepoint initial.alpha := by
  rw [X.width_eq_based, B.initial_metric_eq, B.initial_class_eq]












theorem m67InitialClassFromM02
    {A : GeneralizedSliceCarrier.{u}}
    (S : M59IdentificationSystem.{u})
    (C : SurgerySelectedComponent A)
    (ambient_metric : RiemannianMetric 3 A.carrier)
    (metric : RiemannianMetric 3 C.carrier.carrier)
    (metric_pullback : ∀ x v w,
      ambient_metric.inner (C.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = metric.inner x v w)
    (hM02 : ClosedSimplyConnectedThreeManifoldConclusion
      (M := C.carrier.carrier))
    (hbase : hM02.basepoint = C.basepoint) :
    Nonempty (M67InitialClassData S C ambient_metric) := by
  let pi_two_trivial :
      Subsingleton (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint) :=
    hbase ▸ hM02.pi_two_subsingleton
  let pi_three_integer :
      Nonempty (HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint ≃*
        Multiplicative ℤ) :=
    hbase ▸ hM02.pi_three_integer
  rcases pi_three_integer with ⟨e⟩
  let core := S.core C.compact C.connected C.basepoint pi_two_trivial
  let xi : HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint :=
    e.symm (Multiplicative.ofAdd (1 : ℤ))
  let alpha : HomotopyGroup.Pi 2
      (C1FreeLoopSpace (M := C.carrier.carrier))
      (constantC1Loop C.basepoint) := core.pi_two_pi_three.symm xi
  refine ⟨{ metric := metric
            metric_pullback := metric_pullback
            pi_two_trivial := pi_two_trivial
            alpha := alpha
            nonzero := ?_ }⟩
  intro hzero
  have hxi : xi = 1 := by
    calc
      xi = core.pi_two_pi_three alpha := by simp [alpha]
      _ = 1 := hzero
  have heq : Multiplicative.ofAdd (1 : ℤ) = 1 := by
    calc
      Multiplicative.ofAdd (1 : ℤ) = e xi := by simp [xi]
      _ = e 1 := by rw [hxi]
      _ = 1 := map_one e
  change (1 : ℤ) = 0 at heq
  norm_num at heq













set_option linter.style.haveILetI false in
theorem m67InitialClassFromM02AtSelectedPoint
    {A : GeneralizedSliceCarrier.{u}}
    (S : M59IdentificationSystem.{u})
    (B : M59HigherBasepointTransportService.{u})
    (C : SurgerySelectedComponent A)
    (ambient_metric : RiemannianMetric 3 A.carrier)
    (metric : RiemannianMetric 3 C.carrier.carrier)
    (metric_pullback : ∀ x v w,
      ambient_metric.inner (C.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = metric.inner x v w)
    (hM02 : ClosedSimplyConnectedThreeManifoldConclusion
      (M := C.carrier.carrier)) :
    Nonempty (M67InitialClassData S C ambient_metric) := by
  letI : ConnectedSpace C.carrier.carrier := connectedSpace_iff_univ.mpr C.connected
  letI : LocallyPathConnectedSpace C.carrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 3)) C.carrier.carrier
  letI : PathConnectedSpace C.carrier.carrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  let p := PathConnectedSpace.somePath hM02.basepoint C.basepoint
  let B2 := B.transport 2 (X := C.carrier.carrier)
  let B3 := B.transport 3 (X := C.carrier.carrier)
  have pi_two_trivial :
      Subsingleton (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint) := by
    constructor
    intro a b
    apply Function.LeftInverse.injective (B2.map_left_inverse p.symm)
    exact hM02.pi_two_subsingleton.elim _ _
  obtain ⟨e⟩ := hM02.pi_three_integer
  let xi0 : HomotopyGroup.Pi 3 C.carrier.carrier hM02.basepoint :=
    e.symm (Multiplicative.ofAdd (1 : ℤ))
  have hxi0 : xi0 ≠ 1 := by
    intro hzero
    have heq : Multiplicative.ofAdd (1 : ℤ) = 1 := by
      calc
        Multiplicative.ofAdd (1 : ℤ) = e xi0 := by simp [xi0]
        _ = e 1 := by rw [hzero]
        _ = 1 := map_one e
    change (1 : ℤ) = 0 at heq
    norm_num at heq
  let xi := M59HigherBasepointTransport.map B3 p xi0
  have hxi : xi ≠ 1 := by
    intro hzero
    apply hxi0
    calc
      xi0 = M59HigherBasepointTransport.map B3 p.symm xi :=
        (B3.map_left_inverse p xi0).symm
      _ = M59HigherBasepointTransport.map B3 p.symm 1 := by rw [hzero]
      _ = 1 := B3.map_one p.symm
  let core := S.core C.compact C.connected C.basepoint pi_two_trivial
  let alpha := core.pi_two_pi_three.symm xi
  refine ⟨{ metric := metric
            metric_pullback := metric_pullback
            pi_two_trivial := pi_two_trivial
            alpha := alpha
            nonzero := ?_ }⟩
  change core.pi_two_pi_three alpha ≠ 1
  simpa only [alpha, MulEquiv.apply_symm_apply] using hxi

end PoincareConjecture
