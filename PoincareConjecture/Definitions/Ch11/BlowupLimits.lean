import PoincareConjecture.Definitions.Ch05.Compactness
import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton
import PoincareConjecture.Definitions.Ch04.Pinching
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure GeneralizedSliceCarrier where
  carrier : Type u
  topologicalSpace : TopologicalSpace carrier
  measurableSpace : MeasurableSpace carrier
  borelSpace : @BorelSpace carrier topologicalSpace measurableSpace
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier
  isManifold : IsManifold (𝓡 3) ∞ carrier
  t2Space : T2Space carrier
  t3Space : T3Space carrier
  secondCountable : SecondCountableTopology carrier

attribute [instance] GeneralizedSliceCarrier.topologicalSpace
  GeneralizedSliceCarrier.measurableSpace GeneralizedSliceCarrier.borelSpace
  GeneralizedSliceCarrier.chartedSpace GeneralizedSliceCarrier.isManifold
  GeneralizedSliceCarrier.t2Space GeneralizedSliceCarrier.t3Space
  GeneralizedSliceCarrier.secondCountable

structure GeneralizedRicciFlowBox
    (S : ℝ → GeneralizedSliceCarrier.{u})
    (g : ∀ t : ℝ, RiemannianMetric 3 (S t).carrier) (J : Set ℝ) where
  carrier : GeneralizedSliceCarrier.{u}
  interval : Set ℝ
  relatively_open : ∃ U : Set ℝ, IsOpen U ∧ interval = J ∩ U
  flow : RicciFlow 3 carrier.carrier interval
  forward : ∀ t : ℝ, t ∈ interval → carrier.carrier → (S t).carrier
  inverse : ∀ t : ℝ, t ∈ interval → (S t).carrier → carrier.carrier
  forward_openEmbedding : ∀ t ht, Topology.IsOpenEmbedding (forward t ht)
  forward_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (forward t ht)
  inverse_smooth : ∀ t ht,
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse t ht) (Set.range (forward t ht))
  left_inverse : ∀ t ht, Function.LeftInverse (inverse t ht) (forward t ht)
  right_inverse : ∀ t ht,
    Set.LeftInvOn (forward t ht) (inverse t ht) (Set.range (forward t ht))
  metric_pullback : ∀ t ht x u v,
    (g t).inner (forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x u)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x v) =
      (flow.metric t).inner x u v

structure GeneralizedRicciFlowData where
  slice : ℝ → GeneralizedSliceCarrier.{u}
  interval : Set ℝ
  interval_connected : interval.OrdConnected
  interval_nontrivial : interval.Nontrivial
  slice_nonempty_iff : ∀ t, Nonempty (slice t).carrier ↔ t ∈ interval
  metric : ∀ t : ℝ, RiemannianMetric 3 (slice t).carrier
  connection : ∀ t : ℝ, LeviCivitaData (metric t)
  space_topology : TopologicalSpace (Σ t : ℝ, (slice t).carrier)
  space_t2 : @T2Space (Σ t : ℝ, (slice t).carrier) space_topology
  space_secondCountable :
    @SecondCountableTopology (Σ t : ℝ, (slice t).carrier) space_topology
  time_continuous : @Continuous (Σ t : ℝ, (slice t).carrier) ℝ
    space_topology inferInstance Sigma.fst
  slice_embedding : ∀ t,
    letI := space_topology
    Topology.IsEmbedding (fun x : (slice t).carrier ↦
      (⟨t, x⟩ : Σ s : ℝ, (slice s).carrier))
  box_index : Type u
  box : box_index → GeneralizedRicciFlowBox slice metric interval
  box_openEmbedding : ∀ b,
    letI := space_topology
    Topology.IsOpenEmbedding (fun p : (box b).interval × (box b).carrier.carrier ↦
      (⟨p.1.1, (box b).forward p.1.1 p.1.2 p.2⟩ : Σ t : ℝ, (slice t).carrier))
  box_covers : ∀ t (x : (slice t).carrier),
    ∃ b, ∃ ht : t ∈ (box b).interval, ∃ y, (box b).forward t ht y = x
  vertical_compatibility : ∀ b c t ht hc x y,
    (box b).forward t ht x = (box c).forward t hc y →
    ∀ s hs hs', (box b).forward s hs x = (box c).forward s hs' y

abbrev GeneralizedRicciFlowData.point (F : GeneralizedRicciFlowData) :=
  Σ t : ℝ, (F.slice t).carrier

instance GeneralizedRicciFlowData.pointTopology (F : GeneralizedRicciFlowData) :
    TopologicalSpace F.point := F.space_topology

noncomputable def GeneralizedRicciFlowData.scalar
    (F : GeneralizedRicciFlowData) (p : F.point) : ℝ :=
  (F.connection p.1).scalarCurvature p.2

noncomputable def GeneralizedRicciFlowData.curvatureNorm
    (F : GeneralizedRicciFlowData) (p : F.point) : ℝ :=
  (F.connection p.1).curvatureTensorNorm p.2

structure GeneralizedFlowCylinder (F : GeneralizedRicciFlowData.{u})
    (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ)
    (I : Set ℝ) (U : Set C.carrier) where
  scale_pos : 0 < scale
  forward : ∀ s : ℝ, s ∈ I → C.carrier → (F.slice (origin + s / scale)).carrier
  inverse : ∀ s : ℝ, s ∈ I →
    (F.slice (origin + s / scale)).carrier → C.carrier
  forward_smooth : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (forward s hs) U
  inverse_smooth : ∀ s hs,
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse s hs) (forward s hs '' U)
  left_inverse : ∀ s hs, Set.LeftInvOn (inverse s hs) (forward s hs) U
  right_inverse : ∀ s hs,
    Set.LeftInvOn (forward s hs) (inverse s hs) (forward s hs '' U)
  embedding : Topology.IsEmbedding (fun p : I × U ↦
    (⟨origin + p.1.1 / scale, forward p.1.1 p.1.2 p.2.1⟩ : F.point))
  vertical_compatibility : ∀ (s : ℝ), s ∈ I → ∀ x, x ∈ U →
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' hs', |s' - s| < δ → ∃ hb : origin + s' / scale ∈ (F.box b).interval,
        forward s' hs' x = (F.box b).forward (origin + s' / scale) hb y

noncomputable def GeneralizedFlowCylinder.pointMap {F : GeneralizedRicciFlowData}
    {C : GeneralizedSliceCarrier} {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier) : F.point :=
  ⟨origin + s / scale, e.forward s hs x⟩

noncomputable def GeneralizedFlowCylinder.pullbackInner
    {F : GeneralizedRicciFlowData} {C : GeneralizedSliceCarrier}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) : ℝ :=
  scale * (F.metric (origin + s / scale)).inner (e.forward s hs x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w)

def blowupBackwardInterval (T : ℝ≥0∞) : Set ℝ :=
  {t | t ≤ 0 ∧ ENNReal.ofReal (-t) < T}

structure BlowupLimitFlow (J : Set ℝ) where
  carrier : FlowCarrier.{u} 3
  connectedSpace : @ConnectedSpace carrier.carrier carrier.topologicalSpace
  base : carrier.carrier
  flow : @RicciFlow 3 carrier.carrier carrier.topologicalSpace carrier.chartedSpace
    carrier.isManifold J
  zero_mem : 0 ∈ J
  scalar_normalized :
    letI : TopologicalSpace carrier.carrier := carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier.carrier := carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ carrier.carrier := carrier.isManifold
    (flow.connection 0).scalarCurvature base = 1
  complete :
    letI : TopologicalSpace carrier.carrier := carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier.carrier := carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ carrier.carrier := carrier.isManifold
    ∀ t ∈ J, carrier.metricComplete (flow.metric t)
  nonnegative_curvature_operator :
    letI : TopologicalSpace carrier.carrier := carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier.carrier := carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ carrier.carrier := carrier.isManifold
    ∀ t ∈ J, ∀ x : carrier.carrier,
      LeviCivitaData.NonnegativeCurvatureOperator (flow.connection t) x
  curvature_locally_bounded_in_time :
    letI : TopologicalSpace carrier.carrier := carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier.carrier := carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ carrier.carrier := carrier.isManifold
    ∀ I : Set ℝ, IsCompact I → I ⊆ J → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ I, ∀ x : carrier.carrier,
        |(flow.connection t).curvatureTensorNorm x| ≤ B

def blowupMetricChartDomain {J : Set ℝ} (L : BlowupLimitFlow J)
    (q : L.carrier.carrier) : Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier :=
    L.carrier.chartedSpace
  J ×ˢ (extChartAt (𝓡 3) q).target

def BlowupLimitNoncollapsed {J : Set ℝ} (L : BlowupLimitFlow J) (κ : ℝ) : Prop :=
  let C := L.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  ∀ t ∈ J, ∀ p : C.carrier, ∀ r : ℝ, 0 < r →
    Set.Ioc (t - r ^ 2) t ⊆ J →
    (∀ s ∈ Set.Ioc (t - r ^ 2) t, ∀ q ∈ (L.flow.metric t).ball p r,
      |(L.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
    ENNReal.ofReal (κ * r ^ 3) ≤
      calibratedMetricVolume (L.flow.metric t) ((L.flow.metric t).ball p r)

def BlowupLimitFlow.sliceCarrier {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    GeneralizedSliceCarrier.{u} where
  carrier := L.carrier.carrier
  topologicalSpace := L.carrier.topologicalSpace
  measurableSpace := L.carrier.measurableSpace
  borelSpace := L.carrier.borelSpace
  chartedSpace := L.carrier.chartedSpace
  isManifold := L.carrier.isManifold
  t2Space := L.carrier.t2Space
  t3Space := L.carrier.t3Space
  secondCountable := L.carrier.secondCountable

def GeneralizedKappaNoncollapsedAt (F : GeneralizedRicciFlowData.{u})
    (p : F.point) (κ r₀ : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r ≤ r₀ →
    Set.Ioc (p.1 - r ^ 2) p.1 ⊆ F.interval →
    ∀ e : GeneralizedFlowCylinder F (F.slice p.1) p.1 1
      (Set.Ioc (-r ^ 2) 0) ((F.metric p.1).ball p.2 r),
    (∀ h₀, ∀ x ∈ (F.metric p.1).ball p.2 r,
      e.pointMap 0 h₀ x = (⟨p.1, x⟩ : F.point)) →
    (∀ s hs, ∀ x ∈ (F.metric p.1).ball p.2 r,
      |F.curvatureNorm (e.pointMap s hs x)| ≤ r⁻¹ ^ 2) →
    ENNReal.ofReal (κ * r ^ 3) ≤
      calibratedMetricVolume (F.metric p.1) ((F.metric p.1).ball p.2 r)

structure GeneralizedBlowupSequence where
  flow : ℕ → GeneralizedRicciFlowData.{u}
  base : ∀ k, (flow k).point
  base_scalar_pos : ∀ k, 0 < (flow k).scalar (base k)
  scalar_diverges : Filter.Tendsto (fun k ↦ (flow k).scalar (base k))
    Filter.atTop Filter.atTop

noncomputable def GeneralizedBlowupSequence.scale (S : GeneralizedBlowupSequence)
    (k : ℕ) : ℝ := (S.flow k).scalar (S.base k)

def GeneralizedBlowupSequence.baseBall (S : GeneralizedBlowupSequence)
    (k : ℕ) (A : ℝ) : Set ((S.flow k).slice (S.base k).1).carrier :=
  ((S.flow k).metric (S.base k).1).ball (S.base k).2 (A / Real.sqrt (S.scale k))

def BlowupBaseBallsCompact (S : GeneralizedBlowupSequence) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
    IsCompact (closure (S.baseBall k A))

def GeneralizedBlowupBoundedDistance (S : GeneralizedBlowupSequence) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in Filter.atTop,
    ∀ x ∈ S.baseBall k A,
      (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ D * S.scale k

structure ControlledBlowupCylinder (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (A T B η : ℝ) where
  embedding : GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
    (S.base k).1 (S.scale k) (Set.Icc (-T) 0) (S.baseBall k A)
  zero_identity : ∀ h₀, ∀ x ∈ S.baseBall k A,
    embedding.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point)
  curvature_bound : ∀ s hs, ∀ x ∈ S.baseBall k A,
    |(S.flow k).curvatureNorm (embedding.pointMap s hs x)| ≤ B * S.scale k
  negative_curvature_bound : ∀ s hs, ∀ x ∈ S.baseBall k A,
    let p := embedding.pointMap s hs x
    ((S.flow k).connection p.1).negativeCurvaturePart p.2 ≤ η * S.scale k

structure ShortControlledBlowupHypotheses (S : GeneralizedBlowupSequence.{u})
    (κ r₀ : ℝ) where
  kappa_pos : 0 < κ
  radius_pos : 0 < r₀
  balls_compact : BlowupBaseBallsCompact S
  backward_time : ℝ
  backward_time_pos : 0 < backward_time
  curvature_bound : ℝ
  curvature_bound_nonneg : 0 ≤ curvature_bound
  cylinders : ∀ A : ℝ, 0 < A → ∀ η : ℝ, 0 < η →
    ∀ᶠ k : ℕ in Filter.atTop,
      Nonempty (ControlledBlowupCylinder S k A backward_time curvature_bound η)
  noncollapsed_at_zero : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
    ∀ x ∈ S.baseBall k A,
      GeneralizedKappaNoncollapsedAt (S.flow k) ⟨(S.base k).1, x⟩ κ r₀

structure LongControlledBlowupHypotheses (S : GeneralizedBlowupSequence.{u})
    (κ r₀ : ℝ) (T₀ : ℝ≥0∞) where
  kappa_pos : 0 < κ
  radius_pos : 0 < r₀
  horizon_pos : 0 < T₀
  balls_compact : BlowupBaseBallsCompact S
  cylinders : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T₀ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ η : ℝ, 0 < η →
      ∀ᶠ k : ℕ in Filter.atTop,
        ∃ e : ControlledBlowupCylinder S k A T B η,
          ∀ s hs, ∀ x ∈ S.baseBall k A,
            GeneralizedKappaNoncollapsedAt (S.flow k) (e.embedding.pointMap s hs x) κ r₀

structure BlowupExhaustion {J : Set ℝ} (L : BlowupLimitFlow.{u} J) where
  space : ℕ → Set L.sliceCarrier.carrier
  space_open : ∀ k, IsOpen (space k)
  space_connected : ∀ k, IsConnected (space k)
  space_compactClosure : ∀ k, IsCompact (closure (space k))
  space_increasing : Monotone space
  space_covers : ⋃ k, space k = Set.univ
  base_mem : ∀ k, L.base ∈ space k
  time : ℕ → ℝ
  time_pos : ∀ k, 0 < time k
  time_increasing : Monotone time
  time_subset : ∀ k, Set.Icc (-time k) 0 ⊆ J
  time_cofinal : ∀ I : Set ℝ, IsCompact I → I ⊆ J →
    ∀ᶠ k : ℕ in Filter.atTop, I ⊆ Set.Icc (-time k) 0

noncomputable def blowupPullbackCoefficient {J : Set ℝ}
    {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I U)
    (q : L.sliceCarrier.carrier) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  letI : Decidable (p.1 ∈ I) := Classical.propDecidable _
  if ht : p.1 ∈ I then
    let c := extChartAt (𝓡 3) q
    let D := mfderiv (𝓡 3) (𝓡 3) c.symm p.2
    e.pullbackInner p.1 ht (c.symm p.2)
      (D (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (D (EuclideanSpace.basisFun (Fin 3) ℝ b))
  else 0

structure GeneralizedBlowupConvergence (S : GeneralizedBlowupSequence.{u})
    (J : Set ℝ) where
  limit : BlowupLimitFlow.{u} J
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  exhaustion : BlowupExhaustion limit
  embedding : ∀ k,
    GeneralizedFlowCylinder (S.flow (subsequence k)) limit.sliceCarrier
      (S.base (subsequence k)).1 (S.scale (subsequence k))
      (Set.Icc (-exhaustion.time k) 0) (exhaustion.space k)
  base_preserving : ∀ k h₀,
    (embedding k).pointMap 0 h₀ limit.base = S.base (subsequence k)
  source_balls_in_image : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
    ∀ x ∈ S.baseBall (subsequence k) A, ∃ y ∈ exhaustion.space k,
      ∃ h₀, (embedding k).pointMap 0 h₀ y =
        (⟨(S.base (subsequence k)).1, x⟩ : (S.flow (subsequence k)).point)
  pullback_metric_CInfinity :
    let C := limit.sliceCarrier
    letI : TopologicalSpace limit.carrier.carrier := limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) limit.carrier.carrier :=
      limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ limit.carrier.carrier := limit.carrier.isManifold
    ∀ q : C.carrier, ∀ j r : ℕ,
      ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin 3)), IsCompact K →
      K ⊆ {p | p ∈ blowupMetricChartDomain limit q ∧
        (extChartAt (𝓡 3) q).symm p.2 ∈ exhaustion.space j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        K ⊆ Set.Icc (-exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
        ∀ a b : Fin 3, ∀ p ∈ K,
          ‖iteratedFDerivWithin ℝ r
              (blowupPullbackCoefficient (embedding k) q a b)
              (Set.Icc (-exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) p -
            iteratedFDerivWithin ℝ r
              (FlowCarrier.coordinateCoefficient limit.carrier q
                (fun t x v w ↦ (limit.flow.metric t).inner x v w) a b)
              (blowupMetricChartDomain limit q) p‖ < ε

structure BlowupAncientKappaIdentification
    (L : BlowupLimitFlow (blowupBackwardInterval ⊤)) (κ : ℝ) where
  solution :
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
    AncientKappaSolution 3 C.carrier
  kappa_eq :
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
    solution.kappa = κ
  metric_eq :
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
    ∀ t : ℝ, t ≤ 0 → solution.flow.metric t = L.flow.metric t

end PoincareConjecture
