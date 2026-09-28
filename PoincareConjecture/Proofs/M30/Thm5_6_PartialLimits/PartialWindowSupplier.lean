import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.PartialMetricAdapter
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.PartialWindowService
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SelectedParabolicApplication









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M30



def PartialPointedFlowConvergence.ofM28
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} {F : ∀ k, RicciFlow n (M k) J}
    {p : ∀ k, M k} {A t₀ : ℝ}
    (G : M28.PartialPointedFlowConvergence F p A t₀) :
    PartialPointedFlowConvergence F p A t₀ where
  toPartialPointedMetricConvergence :=
    PartialPointedMetricConvergence.ofM28 G.toPartialPointedMetricConvergence
  baseTime_mem := G.baseTime_mem
  limitFlow := G.limitFlow
  metric_at_baseTime := G.metric_at_baseTime
  spacetime_metric_jets := G.spacetime_metric_jets



def SelectedParabolicApplicationData.toM28
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {tau A : ℝ} (H : SelectedParabolicApplicationData (M := M) tau A) :
    M28.SelectedParabolicApplicationData (M := M) tau A where
  tau_pos := H.tau_pos
  U := H.U
  isOpen_U := H.isOpen_U
  convex_U := H.convex_U
  piece_nonempty := H.piece_nonempty
  embedding := H.embedding
  distance_limit := H.distance_limit
  distance_limit_spec := H.distance_limit_spec
  lipschitz_constant := H.lipschitz_constant
  lipschitz := H.lipschitz
  lower_constant := H.lower_constant
  lower_constant_pos := H.lower_constant_pos
  lower_distance := H.lower_distance
  open_embedding := H.open_embedding
  ball_preconnected := H.ball_preconnected
  smooth := H.smooth
  transition_bounds := H.transition_bounds
  base_index := H.base_index
  base_point := H.base_point
  radius_pos := H.radius_pos
  range_bound := H.range_bound
  compact_cover := H.compact_cover
  flow := H.flow
  distance_eq := H.distance_eq
  metric_jets := H.metric_jets
  positive_ellipticity := H.positive_ellipticity



theorem partialLimitWindowService : PartialLimitWindowService.{u} := by
  intro M _ _ _ tau A H
  obtain ⟨E⟩ := H.toM28.partial_flow
  exact ⟨{
    tau_pos := E.tau_pos
    limit := PartialPointedFlowConvergence.ofM28 E.limit }⟩

end PoincareConjecture.M30
