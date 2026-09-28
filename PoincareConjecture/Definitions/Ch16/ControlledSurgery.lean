import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Definitions.M32HornSelection

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure SurgeryControlSetup (K : MetricSurgeryConstants) where
  standard_initial : StandardInitialMetric
  standard_flow : MaximalStandardCapFlow standard_initial
  standard_lifetime_one : standard_flow.base.lifetime = 1
  epsilon : ℝ
  C : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  epsilon_le : epsilon ≤ min (1 / 200) (K.delta₀ / 2)
  C_pos : 0 < C
  C_large : 1 ≤ C
  C_ge_local : K.C₀ ≤ C
  selector : CommonSurgeryScaleSelector
  selector_delta : ∀ rho delta, 0 < rho → 0 < delta →
    selector.h rho delta ≤ K.delta₀ * rho

noncomputable def surgeryEpochStart (j : ℕ) : ℝ := (2 : ℝ) ^ j / 32

def surgeryEpoch (j : ℕ) : Set ℝ :=
  Set.Ico (surgeryEpochStart j) (surgeryEpochStart (j + 1))

def surgeryEpochEntry (j : ℕ) : Set ℝ :=
  if j = 0 then Set.Ico 0 (surgeryEpochStart 0) else
    Set.Ico (surgeryEpochStart (j - 1)) (surgeryEpochStart j)

structure SurgeryParameterPrefix (K : MetricSurgeryConstants) where
  setup : SurgeryControlSetup K
  i : ℕ
  i_pos : 0 < i
  r : Fin (i + 1) → ℝ
  kappa : Fin (i + 1) → ℝ
  Delta : Fin (i + 1) → ℝ
  r_pos : ∀ j, 0 < r j
  kappa_pos : ∀ j, 0 < kappa j
  Delta_pos : ∀ j, 0 < Delta j
  r_antitone : ∀ ⦃j k⦄, j.val ≤ k.val → r k ≤ r j
  kappa_antitone : ∀ ⦃j k⦄, j.val ≤ k.val → kappa k ≤ kappa j
  Delta_antitone : ∀ ⦃j k⦄, j.val ≤ k.val → Delta k ≤ Delta j
  r_zero : r ⟨0, Nat.zero_lt_succ _⟩ = setup.epsilon
  r_le_epsilon : ∀ j, r j ≤ setup.epsilon
  Delta_le_setup : ∀ j, Delta j ≤ K.delta₀

structure SurgeryObservation (F : SurgeryFlowData.{u}) where
  H : ℝ
  H_pos : 0 < H
  interval_subset : Set.Ico 0 H ⊆ F.time_domain
  standard_flow : MaximalStandardCapFlow F.standard_initial

def SurgeryObservation.redecorate {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F)
    (standard_flow : MaximalStandardCapFlow F.standard_initial) :
    SurgeryObservation F :=
  { H := O.H
    H_pos := O.H_pos
    interval_subset := O.interval_subset
    standard_flow := standard_flow }

def SurgeryObservation.redecorateTo
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hstandard : F.standard_initial = p.setup.standard_initial) :
    SurgeryObservation F :=
  O.redecorate (hstandard ▸ p.setup.standard_flow)

def SurgeryCanonicalOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) (r : ℝ) : Prop :=
  ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
    r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
      SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C

def SurgeryNoncollapsedOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) (kappa : ℝ) : Prop :=
  ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
    ¬ SurgeryPositiveComponentAt F t x →
    ∀ r : ℝ, 0 < r → r ≤ F.parameters.epsilon →
    ∀ e : SurgeryFlowCylinder F (F.slice t) t 1
      (Set.Icc (-r ^ 2) 0) ((F.metric t).ball x r),
      (∀ (h : (0 : ℝ) ∈ Set.Icc (-r ^ 2) 0) y,
        y ∈ (F.metric t).ball x r → HEq (e.forward 0 h y) y) →
      (∀ s hs y, y ∈ (F.metric t).ball x r →
        (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (kappa * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x r)

def SurgeryNoncollapsedAssumptionOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
    ¬ SurgeryPositiveComponentAt F t x →
    ∀ r : ℝ, 0 < r → r ≤ F.parameters.epsilon →
    ∀ e : SurgeryFlowCylinder F (F.slice t) t 1
      (Set.Icc (-r ^ 2) 0) ((F.metric t).ball x r),
      (∀ h y, y ∈ (F.metric t).ball x r → HEq (e.forward 0 h y) y) →
      (∀ s hs y, y ∈ (F.metric t).ball x r →
        (F.connection (t + s / 1)).curvatureTensorNorm
          (e.forward s hs y) ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (F.parameters.kappa t * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x r)

def surgeryObservationInterval {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F) : Set ℝ :=
  Set.Ico 0 O.H

structure SurgeryPrefixControls {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) : Prop where
  standard_initial_eq : F.standard_initial = p.setup.standard_initial
  local_constants_eq : F.local_constants = K
  epsilon_eq : F.parameters.epsilon = p.setup.epsilon
  C_eq : F.parameters.C = p.setup.C
  admissible : SurgeryFlowAdmissible F
  pinched : ∀ t ∈ surgeryObservationInterval O,
    t ∈ F.time_domain → SurgeryPinchedAt (F.connection t) t
  canonical : ∀ (j : Fin (p.i + 1)), j.val ≤ p.i →
    SurgeryCanonicalOn F
      (surgeryObservationInterval O ∩ surgeryEpochEntry j.val) (p.r j)
  noncollapsed : ∀ (j : Fin (p.i + 1)), j.val ≤ p.i →
    SurgeryNoncollapsedOn F (surgeryObservationInterval O ∩ surgeryEpochEntry j.val)
      (p.kappa j)
  delta_bound : ∀ (j : Fin (p.i + 1)), j.val ≤ p.i →
    ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
      F.parameters.delta t ≤ p.Delta j
  r_schedule : ∀ (j : Fin (p.i + 1)), j.val ≤ p.i →
    ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
      F.parameters.r t = p.r j
  kappa_schedule : ∀ (j : Fin (p.i + 1)), j.val ≤ p.i →
    ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
      F.parameters.kappa t = p.kappa j
  h_schedule : ∀ (j : Fin (p.i + 1)), j.val ≤ p.i →
    ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
      F.parameters.h t = p.setup.selector.h
        (F.parameters.delta t * F.parameters.r t)
        (F.parameters.delta t)

def overlapInterval {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : Set ℝ :=
  Set.Ico (surgeryEpochStart (p.i - 1))
    (surgeryEpochStart (p.i + 1))

def prefixFinalInterval {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : Set ℝ :=
  Set.Ico 0 (surgeryEpochStart p.i)

structure SurgeryFixedScalesOn {K : MetricSurgeryConstants}
    (setup : SurgeryControlSetup K) (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (start r deltaUpper : ℝ) : Prop where
  standard_initial_eq : F.standard_initial = setup.standard_initial
  local_constants_eq : F.local_constants = K
  epsilon_eq : F.parameters.epsilon = setup.epsilon
  C_eq : F.parameters.C = setup.C
  r_lower : ∀ t ∈ surgeryObservationInterval O ∩ Set.Ici start,
    r ≤ F.parameters.r t
  delta_le : ∀ t ∈ surgeryObservationInterval O ∩ Set.Ici start,
    F.parameters.delta t ≤ deltaUpper
  h_eq : ∀ t ∈ surgeryObservationInterval O ∩ Set.Ici start,
    F.parameters.h t = setup.selector.h
      (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t)

def SurgeryHighCurvatureAnalyticOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) (r C : ℝ) : Prop :=
  ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
    r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
      scalarGradientNorm (F.metric t) (F.connection t) x ≤
          C * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
        |(F.connection t).laplacian
            (F.connection t).scalarCurvature x +
            2 * (F.connection t).ricciNormSq x| ≤
          C * (F.connection t).scalarCurvature x ^ 2

def SurgeryScalarDerivativeControlOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) (r C : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ hab : a < b, ∀ hJ : Set.Icc a b ⊆ F.time_domain,
    ∀ hS : Disjoint F.surgery_times (Set.Ioc a b),
    ∀ x : (F.slice a).carrier, ∀ t ∈ J ∩ Set.Ioo a b,
      r⁻¹ ^ 2 ≤
          ((F.regular_slabs a b hab hJ hS).flow.connection t).scalarCurvature x →
        ∃ d : ℝ,
          HasDerivAt
            (fun s => ((F.regular_slabs a b hab hJ hS).flow.connection s).scalarCurvature x)
            d t ∧
          |d| ≤ C *
            (((F.regular_slabs a b hab hJ hS).flow.connection t).scalarCurvature x) ^ 2

end PoincareConjecture
