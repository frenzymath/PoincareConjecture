import PoincareConjecture.Proofs.M10.TerminalGradient









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem tangent_eq_of_metric_duals (g : RiemannianMetric n M) {x y : M}
    (hxy : x = y) (X : TangentSpace (𝓡 n) x) (Y : TangentSpace (𝓡 n) y)
    (D : (q : M) → TangentSpace (𝓡 n) q → ℝ)
    (hX : ∀ v, D x v = g.inner x X v) (hY : ∀ v, D y v = g.inner y Y v) :
    hxy ▸ X = Y := by
  subst y
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro v
  exact (hX v).symm.trans (hY v)

variable [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem minimizing_terminal_velocity_eq
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hZ : IsMinimizingBackwardLPath F T 0 τ (G.path Z τ hτ hmax))
    (hW : IsMinimizingBackwardLPath F T 0 τ (G.path W τ hτ hmax))
    (hend : G.gamma Z τ = G.gamma W τ)
    (hl : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ reducedLength F T p q τ)
      (G.gamma Z τ))
    (hsZ : Function.Surjective (G.toLExponentialFamily.sliceDifferential Z τ))
    (hsW : Function.Surjective (G.toLExponentialFamily.sliceDifferential W τ)) :
    hend ▸ curveVelocity (n := n) (G.gamma Z) τ =
      curveVelocity (n := n) (G.gamma W) τ := by
  apply tangent_eq_of_metric_duals (F.metric (T - τ)) hend _ _
    (fun q v ↦ mvfderiv (𝓡 n) (fun x ↦ reducedLength F T p x τ) q v)
  · exact reducedLength_differential_eq_terminal_pairing hL G Z hτ hmax hZ hl hsZ
  · exact reducedLength_differential_eq_terminal_pairing hL G W hτ hmax hW
      (hend ▸ hl) hsW

end PoincareConjecture.M10
