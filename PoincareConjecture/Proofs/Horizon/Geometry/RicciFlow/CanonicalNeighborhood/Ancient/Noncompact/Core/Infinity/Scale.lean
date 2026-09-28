import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Normalization.EscapingDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem AncientKappaSolution.ray_curvature_scale_tendsto_atTop_of_services
    (P : NoncompactKappaServices.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M) (p : M) (ray : ℝ → M)
    (hdistance : ∀ k : ℕ, ((K.flow.metric 0).edist (ray k) p).toReal = k) :
    Tendsto (fun k : ℕ => Real.sqrt ((K.flow.connection 0).scalarCurvature (ray k)) * k)
      atTop atTop := by
  obtain ⟨A⟩ := P.normalization M K p 0 le_rfl
  have hescape : Tendsto
      (fun k : ℕ => ((A.target.flow.metric 0).edist (ray k) p).toReal) atTop atTop := by
    simp only [A.toReal_edist_zero, hdistance]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (Real.sqrt_pos.mpr A.scale_pos)
  have hscale := nonround_curvature_scale_distance_tendsto_atTop_of_services P
    (fun _ : ℕ => A.target) (fun _ => p) (fun k => ray k)
    (fun _ => A.target.not_isRound_of_noncompact (noncompact_univ M))
    (fun _ => A.normalized_scalar) hescape
  convert! hscale using 1
  funext k
  rw [A.scalar_eq 0 le_rfl, zero_div, zero_add, A.toReal_edist_zero, hdistance]
  rw [Real.sqrt_div' _ A.scale_pos.le]
  field_simp [(Real.sqrt_pos.mpr A.scale_pos).ne']

theorem AncientKappaSolution.ray_curvature_scale_tendsto_atTop
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    (K : AncientKappaSolution 3 M) (p : M) (ray : ℝ → M)
    (hdistance : ∀ k : ℕ, ((K.flow.metric 0).edist (ray k) p).toReal = k) :
    Tendsto (fun k : ℕ => Real.sqrt ((K.flow.connection 0).scalarCurvature (ray k)) * k)
      atTop atTop := by
  exact AncientKappaSolution.ray_curvature_scale_tendsto_atTop_of_services P.noncompactServices K p ray hdistance

end PoincareConjecture
