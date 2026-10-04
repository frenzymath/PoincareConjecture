import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareLib.Geometry.RicciFlow.Soliton.Basic

/-!
# M19 two-dimensional classification data

The alternatives are dimension-specific and do not inherit the 3D quotient or
orientation assumptions.  The two-dimensional kappa classification is kept
separate from the later three-dimensional model ledger.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- A compact round ancient two-dimensional kappa-solution certificate. -/
structure TwoDimensionalAncientRoundCertificate
    (K : AncientKappaSolution 2 M) where
  compact : CompactSpace M
  round_at_all_times : ∀ t : ℝ, t ≤ 0 →
    ConstantPositiveSectionalCurvature (K.flow.metric t) (K.flow.connection t)

/-! The roundness output for an actual M18 asymptotic limit.  The bounded
curvature and homothety fields are included here because Remark 9.12 defers
both properties until the two-dimensional argument of Corollary 9.50. -/
structure TwoDimensionalAsymptoticRoundCertificate
    {K : AncientKappaSolution 2 M} (S : AncientRescalingSequence K)
    (L : AncientAsymptoticSolitonLimitData S) where
  bounded_curvature :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : C.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B
  self_similar :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 →
      Nonempty (HomotheticMetricSlice
        (L.convergence.limit.flow.metric (-1))
        (L.convergence.limit.flow.metric t) |t|)
  compact :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    CompactSpace C.carrier
  round_at_all_times :
    ∀ t : ℝ, t < 0 →
      let C := L.convergence.limit.carrier
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
      ConstantPositiveSectionalCurvature
        (L.convergence.limit.flow.metric t)
        (L.convergence.limit.flow.connection t)

/-- The compact/noncompact alternatives for a 2D shrinking soliton. -/
inductive TwoDimensionalSolitonModel
    (S : GradientShrinkingSolitonData 2 M)
    (G : ShrinkingSolitonFlow S) : Type (u + 2) where
  | compactRound : CompactRoundShrinkingModel G → TwoDimensionalSolitonModel S G

structure TwoDimensionalShrinkingSolitonConclusion
    (S : GradientShrinkingSolitonData 2 M) where
  flow : ShrinkingSolitonFlow S
  model : TwoDimensionalSolitonModel S flow

end PoincareMT
