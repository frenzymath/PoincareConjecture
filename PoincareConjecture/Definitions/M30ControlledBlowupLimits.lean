import PoincareConjecture.Definitions.M29GeneralizedDistance
import PoincareConjecture.Definitions.Ch11.BlowupLimits









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



noncomputable def m30BackwardDuration
    (S : GeneralizedBlowupSequence.{u}) (k : ℕ)
    (x : ((S.flow k).slice (S.base k).1).carrier) (mu : ℝ) : ℝ :=
  mu * S.scale k /
    max (S.scale k) ((S.flow k).scalar ⟨(S.base k).1, x⟩)




structure GeneralizedMaximalBackwardFlowLine
    (F : GeneralizedRicciFlowData.{u}) (p : F.point)
    (scale duration : ℝ) where
  maximal_interval : Set ℝ
  maximal_interval_mem_zero : 0 ∈ maximal_interval
  maximal_interval_ordConnected : maximal_interval.OrdConnected
  embedding : GeneralizedFlowCylinder F (F.slice p.1) p.1 scale
    maximal_interval ({p.2} : Set (F.slice p.1).carrier)
  zero_identity :
    embedding.pointMap 0 maximal_interval_mem_zero p.2 = p
  requested_interval_subset :
    Set.Icc (-duration) 0 ⊆ maximal_interval
  maximal : ∀ (I' : Set ℝ)
    (_e' : GeneralizedFlowCylinder F (F.slice p.1) p.1 scale I'
      ({p.2} : Set (F.slice p.1).carrier)),
    I'.OrdConnected →
    ∀ hI : maximal_interval ⊆ I',
      (∀ s (hs : s ∈ maximal_interval),
        _e'.pointMap s (hI hs) p.2 = embedding.pointMap s hs p.2) →
      I' = maximal_interval



def GeneralizedMaximalBackwardFlowLineSurvival
    (S : GeneralizedBlowupSequence.{u}) (mu : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
    ∀ x ∈ S.baseBall k A,
      Nonempty (GeneralizedMaximalBackwardFlowLine
        (S.flow k) ⟨(S.base k).1, x⟩ (S.scale k)
        (m30BackwardDuration S k x mu))




structure M30FiniteHorizonSlab
    (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (A T kappa r₀ : ℝ) where
  embedding : GeneralizedFlowCylinder (S.flow k)
    ((S.flow k).slice (S.base k).1) (S.base k).1 (S.scale k)
    (Set.Ioc (-T) 0) (S.baseBall k A)
  zero_identity : ∀ h₀, ∀ x ∈ S.baseBall k A,
    embedding.pointMap 0 h₀ x =
      (⟨(S.base k).1, x⟩ : (S.flow k).point)
  noncollapsed : ∀ s hs, ∀ x ∈ S.baseBall k A,
    GeneralizedKappaNoncollapsedAt
      (S.flow k) (embedding.pointMap s hs x) kappa r₀




structure M30CommonBlowupControls
    (S : GeneralizedBlowupSequence.{u})
    (epsilon C kappa r₀ mu : ℝ) where
  epsilon_pos : 0 < epsilon
  C_pos : 0 < C
  kappa_pos : 0 < kappa
  radius_pos : 0 < r₀

  branch : ∀ k, generalizedPinchedOrNonnegative (S.flow k)
  canonical : ∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
    (S.flow k) epsilon C (S.base k).1 (S.base k).2


  analytic_constant : ℝ
  analytic_constant_pos : 0 < analytic_constant
  scalar_gradient_bound : ∀ k t, t ∈ (S.flow k).interval → t ≤ (S.base k).1 →
    ∀ x : ((S.flow k).slice t).carrier,
      4 * S.scale k ≤ ((S.flow k).connection t).scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, ((S.flow k).metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) ((S.flow k).connection t).scalarCurvature x v| ≤
          analytic_constant * ((S.flow k).connection t).scalarCurvature x ^ (3 / 2 : ℝ)
  scalar_time_derivative_bound : ∀ k b t,
    t ∈ ((S.flow k).box b).interval → t ≤ (S.base k).1 →
    ∀ x : ((S.flow k).box b).carrier.carrier,
      4 * S.scale k ≤ (((S.flow k).box b).flow.connection t).scalarCurvature x →
      ∃ d : ℝ, HasDerivWithinAt
        (fun s : ℝ => (((S.flow k).box b).flow.connection s).scalarCurvature x) d
        ((S.flow k).box b).interval t ∧
          |d| ≤ analytic_constant *
            (((S.flow k).box b).flow.connection t).scalarCurvature x ^ 2
  balls_compact : BlowupBaseBallsCompact S
  noncollapsed_at_zero : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
    ∀ x ∈ S.baseBall k A,
      GeneralizedKappaNoncollapsedAt
        (S.flow k) ⟨(S.base k).1, x⟩ kappa r₀
  mu_pos : 0 < mu
  maximal_worldlines : GeneralizedMaximalBackwardFlowLineSurvival S mu


structure M30LongBlowupControls
    (S : GeneralizedBlowupSequence.{u})
    (epsilon C kappa r₀ mu : ℝ) (T₀ : ℝ≥0∞)
    extends M30CommonBlowupControls S epsilon C kappa r₀ mu where
  horizon_pos : 0 < T₀
  slabs : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
    ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
      Nonempty (M30FiniteHorizonSlab S k A T kappa r₀)






structure M30GeometricLongControls
    (S : GeneralizedBlowupSequence.{u}) (T₀ : ℝ≥0∞) where
  horizon_pos : 0 < T₀
  balls_compact : BlowupBaseBallsCompact S
  terminal_volume : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧
    ∀ᶠ k : ℕ in Filter.atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1)
          (S.baseBall k rho)
  cylinders : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k : ℕ in Filter.atTop,
        Nonempty (ControlledBlowupCylinder S k A T B eta)



def M30LimitNoncollapsedAtScale
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) (kappa r₀ : ℝ) : Prop :=
  let C := L.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  ∀ t ∈ J, ∀ p : C.carrier, ∀ r : ℝ, 0 < r → r ≤ r₀ →
    Set.Ioc (t - r ^ 2) t ⊆ J →
    (∀ s ∈ Set.Ioc (t - r ^ 2) t, ∀ q ∈ (L.flow.metric t).ball p r,
      |(L.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (L.flow.metric t) ((L.flow.metric t).ball p r)




structure M30AncientKappaIdentification
    (L : BlowupLimitFlow (blowupBackwardInterval ⊤)) (kappa : ℝ) where
  certificate : BlowupAncientKappaIdentification L kappa
  domain_eq : blowupBackwardInterval ⊤ = Set.Iic 0
  connection_eq :
    let C := L.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : ConnectedSpace C.carrier := L.connectedSpace
    ∀ t : ℝ, t ≤ 0 →
      HEq (certificate.solution.flow.connection t)
        (L.flow.connection t)

end PoincareConjecture
