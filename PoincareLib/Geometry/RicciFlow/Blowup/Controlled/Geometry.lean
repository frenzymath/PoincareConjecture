import PoincareLib.Geometry.RicciFlow.Blowup.Sequence
import PoincareLib.Geometry.RicciFlow.Generalized.Cylinder
import PoincareLib.Geometry.RicciFlow.AncientKappa.Basic
import PoincareLib.Geometry.RicciFlow.Pinching.Definitions

/-!
Adapted from Mapher `PoincareMT/Definitions/Ch11/BlowupLimits.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators intervalIntegral

universe u

namespace PoincareMT

noncomputable def GeneralizedRicciFlowData.curvatureNorm
    (F : GeneralizedRicciFlowData) (p : F.point) : ℝ :=
  (F.connection p.1).curvatureTensorNorm p.2


def blowupBackwardInterval (T : ℝ≥0∞) : Set ℝ :=
  {t | t ≤ 0 ∧ ENNReal.ofReal (-t) < T}

/-- A normalized complete limit with curvature bounded uniformly in space on
each compact time interval.  In particular, the final slice is complete and
has globally bounded nonnegative curvature. -/
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

/-- The coordinate domain used for metric jets.  Derivatives are taken within
this domain, so a total metric representative outside the flow interval does
not determine the endpoint derivatives. -/
def blowupMetricChartDomain {J : Set ℝ} (L : BlowupLimitFlow J)
    (q : L.carrier.carrier) : Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier :=
    L.carrier.chartedSpace
  J ×ˢ (extChartAt (𝓡 3) q).target

/-- All-scales noncollapsing of the actual limiting flow.  The hypothesis
includes existence of the whole backward parabolic cylinder in its time
domain, and the volume uses the selected metric at its top time. -/
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

/-- The carrier of a limit, viewed without a connectedness requirement. -/
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

/-- Parabolic noncollapsing at one spacetime point.  This is a genuine volume
lower bound whenever the backward cylinder exists and has the indicated
curvature bound; positive curvature is not a substitute for this condition. -/
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

def BlowupBaseBallsCompact (S : GeneralizedBlowupSequence) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
    IsCompact (closure (S.baseBall k A))

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

/-- Short-time analytic controls after the bounded-distance and canonical
neighborhood arguments.  The same `T,B` work on every fixed normalized ball;
the index beyond which they work may depend on its radius and error. -/
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

/-- Controls on every finite backward slab below the prescribed horizon.
Every point of each displayed cylinder satisfies the actual volume condition. -/
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

/-- An exhaustion of the limiting space and of its backward time interval. -/
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

/-- A local-coordinate coefficient of a rescaled source metric.  The zero
extension is ignored by the within-domain derivatives in the convergence
definition. -/
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

/-- Pointed smooth convergence of the rescaled generalized flows, with
expanding source images and actual pullback metric jets. -/
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

/-- Identification of an infinite-horizon limit with an actual ancient
kappa-solution on the same carrier and the same metric at every ancient time. -/
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


end PoincareMT
