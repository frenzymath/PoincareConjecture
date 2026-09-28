import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.IntrinsicBounds.Global

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace LExponentialGeometry

theorem reducedLength_eq_action_on_regularDomain {J : Set ℝ} {F : RicciFlow n M J}
    {T R : ℝ} {p : M} (G : LExponentialGeometry F T R p)
    {Z : TangentSpace (𝓡 n) p} {τ : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain) :
    reducedLength F T p (G.gamma Z τ) τ = G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ) := by
  have hs : (Z, τ) ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have ht : (G.gamma Z τ, τ) ∈ G.regular_chart.target :=
    G.regular_forward (Z, τ) ▸ G.regular_chart.map_source hs
  let r := G.regular_point (G.gamma Z τ, τ) ht
  have hr := r.representative_eq (G.gamma Z τ, τ) r.center_mem
  rw [G.regular_point_representative] at hr
  have hinv : G.regular_chart.symm (G.gamma Z τ, τ) = (Z, τ) := by
    rw [← G.regular_forward (Z, τ)]
    exact G.regular_chart.left_inv hs
  simpa only [hinv] using hr.symm

end LExponentialGeometry

namespace AncientAsymptoticSolitonPredecessors

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem backwardLIntegrand_nonneg (P : AncientAsymptoticSolitonPredecessors K)
    (γ : ℝ → M) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ backwardLIntegrand K.flow 0 γ τ := by
  have hscalar := ((Classical.choice P.structural).structural M K).scalar_pos (0 - τ)
    (by linarith) (γ τ)
  have hinner : 0 ≤ (K.flow.metric (0 - τ)).inner (γ τ)
      (curveVelocity γ τ) (curveVelocity γ τ) := by
    by_cases hv : curveVelocity (n := n) γ τ = 0
    · simp [hv]
    · exact ((K.flow.metric (0 - τ)).pos _ _ hv).le
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hscalar.le hinner)

theorem regular_path_reducedLength_mul_sqrt_le
    (P : AncientAsymptoticSolitonPredecessors K)
    {R : ℝ} {p : M} (G : LExponentialGeometry K.flow 0 R p)
    {Z : TangentSpace (𝓡 n) p} {τ s : ℝ}
    (hreg : (Z, τ) ∈ G.toLExponentialFamily.regularDomain)
    (hs : 0 < s) (hsτ : s ≤ τ) :
    reducedLength K.flow 0 p (G.gamma Z s) s * Real.sqrt s ≤
      reducedLength K.flow 0 p (G.gamma Z τ) τ * Real.sqrt τ := by
  have hτ := hreg.1.choose
  have hR := hreg.1.choose_spec.choose
  have hsub : Icc s τ ⊆ Ioo 0 R := fun t ht =>
    ⟨hs.trans_le ht.1, ht.2.trans_lt hR⟩
  have hd (t : ℝ) (ht : t ∈ Icc s τ) :=
    G.action_time_derivative Z t (hsub ht).1 (hsub ht).2
  have hmono : MonotoneOn (G.toLExponentialFamily.action Z) (Icc s τ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s τ)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact P.backwardLIntegrand_nonneg _ (hsub (interior_subset ht)).1.le
  have h := hmono ⟨le_rfl, hsτ⟩ ⟨hsτ, le_rfl⟩ hsτ
  rw [G.reducedLength_eq_action_on_regularDomain (G.backward_nesting Z τ hreg s hs hsτ),
    G.reducedLength_eq_action_on_regularDomain hreg]
  have hsqr := (Real.sqrt_pos.mpr hs).ne'
  have htqr := (Real.sqrt_pos.mpr hτ).ne'
  field_simp
  nlinarith

end AncientAsymptoticSolitonPredecessors

end PoincareConjecture
