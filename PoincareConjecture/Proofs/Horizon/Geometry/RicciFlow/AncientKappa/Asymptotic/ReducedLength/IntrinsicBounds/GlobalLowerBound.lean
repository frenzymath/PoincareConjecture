import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.PathDistance.LowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.RegularImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem distance_sq_le_reducedLength
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ) :
    ((K.flow.metric (-τ)).edist x y).toReal ^ 2 ≤
      16 * (2 * (n : ℝ) + 604) ^ 2 *
        (reducedLength K.flow 0 p x τ + reducedLength K.flow 0 p y τ + 1) * τ := by
  let Q := Classical.choice (P.reduced_length (τ + 1) (by linarith))
  let G := Classical.choice (Q.exponential_geometry p)
  have hdense := G.dense_regularImage_slice Q hτ (by linarith : τ < τ + 1)
  let g := K.flow.metric (-τ)
  let := g.toMetricSpace
  let B : Set (M × M) := {z | dist z.1 z.2 ^ 2 ≤
    16 * (2 * (n : ℝ) + 604) ^ 2 *
      (reducedLength K.flow 0 p z.1 τ + reducedLength K.flow 0 p z.2 τ + 1) * τ}
  have hc := P.continuous_reducedLength p τ hτ
  have hclosed : IsClosed B := isClosed_le (continuous_dist.pow 2)
    ((continuous_const.mul (((hc.comp continuous_fst).add
      (hc.comp continuous_snd)).add continuous_const)).mul continuous_const)
  have hsub : {q | (q, τ) ∈ G.regularImage} ×ˢ {q | (q, τ) ∈ G.regularImage} ⊆ B := by
    intro z hz
    obtain ⟨Z, hZ, heZ⟩ := G.exists_regular_initial_of_mem_regularImage hz.1
    obtain ⟨W, hW, heW⟩ := G.exists_regular_initial_of_mem_regularImage hz.2
    have h := P.regular_endpoints_distance_sq_le_reducedLength G hZ hW
    rw [heZ, heW] at h
    exact h
  exact closure_minimal hsub hclosed ((hdense.prod hdense) (x, y))

theorem reducedLength_intrinsic_lower_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x y : M) {τ : ℝ} (hτ : 0 < τ) :
    ((K.flow.metric (-τ)).edist x y).toReal ^ 2 /
        (16 * (2 * (n : ℝ) + 604) ^ 2 * τ) - reducedLength K.flow 0 p x τ - 1 ≤
      reducedLength K.flow 0 p y τ := by
  have h := P.distance_sq_le_reducedLength p x y hτ
  have hden : 0 < 16 * (2 * (n : ℝ) + 604) ^ 2 * τ := by positivity
  have hd := (div_le_iff₀ hden).mpr (by nlinarith :
    ((K.flow.metric (-τ)).edist x y).toReal ^ 2 ≤
      (reducedLength K.flow 0 p x τ + reducedLength K.flow 0 p y τ + 1) *
        (16 * (2 * (n : ℝ) + 604) ^ 2 * τ))
  linarith

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
