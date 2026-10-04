import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.MissingCompletionRadius
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckPrecompactBalls
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenMetricBalls
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicMetricSpace

/-!
# Completion-radius bounds on every actual neck central point

The proved neck ball and exact open-subtype ball identities give compact
closure in the unchanged recut metric. The missing endpoint therefore
lies at least the actual neck buffer radius away from every central
sphere point. Source: Morgan--Tian Lemma 10.27, p. 261; derivation 155.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

/-- The exact buffer radius is a lower bound at every central-sphere
point, in the same original open-region metric. The second bound uses
only the frozen `epsilon < 1/2` field. Derivation 155. -/
theorem neck_completion_radius_lower
    (N : EpsilonNeck g) (U : TopologicalSpace.Opens M)
    (hNU : N.carrier ⊆ (U : Set M))
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      ∀ x : U, (x : M) ∈ N.central_sphere →
        N.scale * N.epsilon⁻¹ / 8 ≤ dist (x : UniformSpace.Completion U) E ∧
          N.scale / 4 < dist (x : UniformSpace.Completion U) E := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside x hx
  let rho : ℝ := N.scale * N.epsilon⁻¹ / 8
  have hrho : 0 < rho := neck_shortening_saving_pos N
  obtain ⟨hcompact, hclosure⟩ := N.precompact_ball_of_central_sphere hx
  have hclosureU : closure (g.ball (x : M) rho) ⊆ (U : Set M) :=
    hclosure.trans hNU
  have hballU : g.ball (x : M) rho ⊆ (U : Set M) :=
    subset_closure.trans hclosureU
  have hprecompact : IsCompact (closure ((intrinsicOpenMetric g U).ball x rho)) := by
    rw [intrinsicOpenMetric_closure_ball_eq_preimage g U x hballU]
    exact Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
      (fun z hz => ⟨⟨z, hclosureU hz⟩, rfl⟩)
  have hball : Metric.ball x rho = (intrinsicOpenMetric g U).ball x rho := by
    ext q
    change dist q x < rho ↔ (intrinsicOpenMetric g U).edist x q < ENNReal.ofReal rho
    have hed : (intrinsicOpenMetric g U).edist x q = ENNReal.ofReal (dist x q) := by
      change edist x q = _
      exact edist_dist x q
    rw [hed, ENNReal.ofReal_lt_ofReal_iff hrho, dist_comm]
  have hlower : rho ≤ dist (x : UniformSpace.Completion U) E :=
    UniformSpace.Completion.radius_le_dist_of_precompact_ball E houtside x
      (hball.symm ▸ hprecompact)
  have hinv : (2 : ℝ) < N.epsilon⁻¹ := by
    have h := one_div_lt_one_div_of_lt N.epsilon_pos N.epsilon_lt_half
    norm_num [one_div] at h
    exact h
  have hscale : N.scale / 4 < rho := by
    have hmul := mul_lt_mul_of_pos_left hinv N.scale_pos
    dsimp only [rho]
    linarith only [hmul]
  exact ⟨hlower, hscale.trans_le hlower⟩

end PoincareMT.M28
