import PoincareConjecture.Definitions.Ch05.Compactness
import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton
import PoincareConjecture.Definitions.Ch09.AsymptoticVolume
import PoincareConjecture.Definitions.Ch09.ShrinkingSoliton
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure BasedKappaSolution (kappa : ℝ) where
  carrier : FlowCarrier 3
  connectedSpace : @ConnectedSpace carrier.carrier carrier.topologicalSpace
  flow :
    let C := carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : ConnectedSpace C.carrier := connectedSpace
    AncientKappaSolution 3 C.carrier
  base : carrier.carrier
  kappa_eq :
    let C := carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : ConnectedSpace C.carrier := connectedSpace
    flow.kappa = kappa
  scalar_normalized :
    let C := carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : ConnectedSpace C.carrier := connectedSpace
    (flow.flow.connection 0).scalarCurvature base = 1

structure NormalizedKappaSolutionSequence (kappa : ℝ) where
  kappa_pos : 0 < kappa
  term : ℕ → BasedKappaSolution kappa

structure NormalizedKappaSpacetimeEmbedding
    {kappa : ℝ} {source target : BasedKappaSolution kappa}
    (domain : Set (ℝ × target.carrier.carrier)) where
  toFun : ℝ × target.carrier.carrier → ℝ × source.carrier.carrier
  time_preserving : ∀ t x, (toFun (t, x)).1 = t
  injective_on : Set.InjOn toFun domain
  inverse : ℝ × source.carrier.carrier → ℝ × target.carrier.carrier
  left_inverse : ∀ p ∈ domain, inverse (toFun p) = p
  right_inverse : ∀ q ∈ toFun '' domain, toFun (inverse q) = q
  smooth_on :
    let C := target.carrier
    let D := source.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 3) ∞ D.carrier := D.isManifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
      toFun domain
  smooth_inverse_on :
    let C := target.carrier
    let D := source.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 3) ∞ D.carrier := D.isManifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
      inverse (toFun '' domain)

noncomputable def normalizedKappaPullbackInnerValue
    {kappa : ℝ} {source target : BasedKappaSolution kappa}
    {domain : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (t : ℝ) (x : target.carrier.carrier)
    (v w : target.carrier.tangent x) : ℝ :=
  let C := target.carrier
  let D := source.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : MeasurableSpace D.carrier := D.measurableSpace
  letI : BorelSpace D.carrier := D.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 3) ∞ D.carrier := D.isManifold
  letI : T2Space D.carrier := D.t2Space
  letI : T3Space D.carrier := D.t3Space
  letI : SecondCountableTopology D.carrier := D.secondCountable
  letI : ConnectedSpace D.carrier := source.connectedSpace
  let ψ : target.carrier.carrier → source.carrier.carrier :=
    fun y => (e.toFun (t, y)).2
  (source.flow.flow.metric t).inner (ψ x)
    (mfderiv (𝓡 3) (𝓡 3) ψ x v)
    (mfderiv (𝓡 3) (𝓡 3) ψ x w)

noncomputable def normalizedKappaPullbackCoefficient
    {kappa : ℝ} {source target : BasedKappaSolution kappa}
    {domain : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (q : target.carrier.carrier) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let C := target.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 3) q
  let A := mfderiv (𝓡 3) (𝓡 3) c.symm p.2
  normalizedKappaPullbackInnerValue e p.1 (c.symm p.2)
    (A (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (A (EuclideanSpace.basisFun (Fin 3) ℝ b))

structure NormalizedKappaGeometricConvergence
    {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa) where
  limit : BasedKappaSolution kappa
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  exhaustion : ℕ → Set limit.carrier.carrier
  exhaustion_open : ∀ j,
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsOpen (exhaustion j)
  exhaustion_connected : ∀ j,
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsConnected (exhaustion j)
  exhaustion_compactClosure : ∀ j,
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsCompact (closure (exhaustion j))
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = Set.univ
  embedding : ∀ j,
    NormalizedKappaSpacetimeEmbedding
      (source := S.term (subsequence j)) (target := limit)
      (Set.Iic 0 ×ˢ exhaustion j)
  base_preserving : ∀ j,
    (embedding j).toFun (0, limit.base) =
      (0, (S.term (subsequence j)).base)
  pullback_metric_CInfinity :
    let C := limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : ConnectedSpace C.carrier := limit.connectedSpace
    ∀ q : C.carrier, ∀ j r : ℕ,
      ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin 3)), IsCompact K →
      K ⊆ {p | p.1 ≤ 0 ∧ p.2 ∈ (extChartAt (𝓡 3) q).target ∧
        (extChartAt (𝓡 3) q).symm p.2 ∈ exhaustion j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin 3, ∀ p ∈ K,
          ‖MetricJet r
              (normalizedKappaPullbackCoefficient
                (source := S.term (subsequence k)) (target := limit)
                (embedding k) q a b) K p -
            MetricJet r
              (FlowCarrier.coordinateCoefficient C q
                (fun t x v w ↦
                  (limit.flow.flow.metric t).inner x v w) a b) K p‖ < ε

end PoincareConjecture
