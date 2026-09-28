import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRoundComponent

open SingularRegularLimit.RoundComparison

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ}



theorem scale_bounds_of_contains (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g) (hepsilon : epsilon ≤ roundComparisonThreshold)
    {x : M} (hx : x ∈ N.carrier) :
    D.scalarCurvature x / 7 < N.scale ∧ N.scale < D.scalarCurvature x / 5 := by
  have h := N.normalized_scalar_close D hepsilon (N.inverse x)
  rw [N.right_inverse hx, inv_mul_eq_div] at h
  obtain ⟨hl, hu⟩ := abs_lt.mp h
  have hl' : 5 * N.scale < D.scalarCurvature x :=
    (lt_div_iff₀ N.scale_pos).mp (by linarith)
  have hu' : D.scalarCurvature x < 7 * N.scale :=
    (div_lt_iff₀ N.scale_pos).mp (by linarith)
  constructor <;> linarith

end PoincareConjecture.SingularRoundComponent

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit.RoundComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem eventually_roundComponent_scale_bounds
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold) (x : H.regularRegion P04)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ∀ᶠ t in 𝓝[<] T,
      ∀ N : SingularRoundComponent ((H.terminalFlow P04).metric t) H.epsilon,
        x ∈ N.carrier →
        (H.terminalConnection P04).scalarCurvature x / 14 < N.scale ∧
        N.scale < 2 * (H.terminalConnection P04).scalarCurvature x / 5 := by
  have hscalar := H.tendsto_terminal_scalarCurvature P04 x
  have hlow : ∀ᶠ t in 𝓝[<] T,
      (H.terminalConnection P04).scalarCurvature x / 2 < H.reference.scalar t x :=
    hscalar.eventually (eventually_gt_nhds (by linarith :
      (H.terminalConnection P04).scalarCurvature x / 2 <
        (H.terminalConnection P04).scalarCurvature x))
  have hupp : ∀ᶠ t in 𝓝[<] T,
      H.reference.scalar t x < 2 * (H.terminalConnection P04).scalarCurvature x :=
    hscalar.eventually (eventually_lt_nhds (by linarith :
      (H.terminalConnection P04).scalarCurvature x <
        2 * (H.terminalConnection P04).scalarCurvature x))
  filter_upwards [hlow, hupp, self_mem_nhdsWithin] with t hlow hupp ht
  intro N hx
  obtain ⟨hscale, hscale'⟩ := N.scale_bounds_of_contains
    ((H.terminalFlow P04).connection t) hepsilon hx
  rw [H.terminalFlow_scalar_of_ne P04 ht.ne] at hscale hscale'
  constructor <;> linarith

end PoincareConjecture.SingularTimeAssumptions
