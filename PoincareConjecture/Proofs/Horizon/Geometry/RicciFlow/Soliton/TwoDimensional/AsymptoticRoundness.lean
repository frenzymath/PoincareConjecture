import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Asymptotic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.RoundFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Roundness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Classification

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M} {S : AncientRescalingSequence K}

theorem round (L : AncientAsymptoticSolitonLimitData S) {t : ℝ} (ht : t < 0) :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ConstantPositiveSectionalCurvature
      (L.convergence.limit.flow.metric t) (L.convergence.limit.flow.connection t) := by
  let C := L.convergence.limit.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
  let : T3Space C.carrier := C.t3Space
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  let : ConnectedSpace C.carrier := ⟨⟨L.convergence.limit.base⟩⟩
  let : CompactSpace C.carrier := L.compactSpace
  let D := L.convergence.limit.flow.connection t
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 (fun x => L.potential (x, t)) :=
    (L.potential_slice_smooth ht).of_le (by decide)
  apply D.constantPositiveSectionalCurvature_of_compact_surface_soliton
    (lambda := -(1 / (2 * t))) (neg_pos.mpr (one_div_neg.mpr (by linarith))) hf
  · intro x v w
    have h := L.soliton_equation t ht x v w
    dsimp [D] at *
    linarith
  · intro x
    exact D.scalar_nonnegative_of_nonnegative_curvatureOperator x
      (L.convergence.limit.nonnegative_curvature_operator t ht x)

theorem scalar_eq_neg_inv_of_round (L : AncientAsymptoticSolitonLimitData S)
    {t : ℝ} (ht : t < 0)
    (hround :
      let C := L.convergence.limit.carrier
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
      ConstantPositiveSectionalCurvature
        (L.convergence.limit.flow.metric t) (L.convergence.limit.flow.connection t)) :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ∀ x : C.carrier, (L.convergence.limit.flow.connection t).scalarCurvature x = -1 / t := by
  let C := L.convergence.limit.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
  let : CompactSpace C.carrier := L.compactSpace
  change ∀ x : C.carrier, _
  intro x
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 (fun y => L.potential (y, t)) :=
    (L.potential_slice_smooth ht).of_le (by decide)
  have heq := (L.convergence.limit.flow.connection t).scalar_eq_twice_scale_of_compact_round_soliton
    hf (lambda := -(1 / (2 * t))) (fun y v w => by
      have h := L.soliton_equation t ht y v w
      linarith) hround x
  convert heq using 1
  ring

theorem roundCertificate_of_round (L : AncientAsymptoticSolitonLimitData S)
    (hround : ∀ t : ℝ, t < 0 →
      let C := L.convergence.limit.carrier
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
      ConstantPositiveSectionalCurvature
        (L.convergence.limit.flow.metric t) (L.convergence.limit.flow.connection t)) :
    TwoDimensionalAsymptoticRoundCertificate S L where
  bounded_curvature := L.bounded_curvature
  compact := L.compactSpace
  round_at_all_times := hround
  self_similar := by
    let C := L.convergence.limit.carrier
    let : TopologicalSpace C.carrier := C.topologicalSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    exact L.convergence.limit.flow.homotheticMetricSlice_of_scalarCurvature
      (fun t ht => L.scalar_eq_neg_inv_of_round ht (hround t ht))

theorem roundCertificate (L : AncientAsymptoticSolitonLimitData S) :
    TwoDimensionalAsymptoticRoundCertificate S L :=
  L.roundCertificate_of_round (fun _ ht => L.round ht)

end PoincareConjecture.AncientAsymptoticSolitonLimitData

namespace PoincareConjecture.TwoDimensionalClassificationPredecessors

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem asymptoticRoundTheory (P : TwoDimensionalClassificationPredecessors (M := M))
    (K : AncientKappaSolution 2 M) : Nonempty (TwoDimensionalAsymptoticRoundTheory K) := by
  refine ⟨⟨fun S => ?_⟩⟩
  obtain ⟨L⟩ := P.m18 K S
  exact ⟨L, L.roundCertificate⟩

end PoincareConjecture.TwoDimensionalClassificationPredecessors
