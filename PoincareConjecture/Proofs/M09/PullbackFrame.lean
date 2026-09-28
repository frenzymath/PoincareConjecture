import PoincareConjecture.Proofs.M09.ParametricFrame
import PoincareConjecture.Proofs.M09.ParametricCurveDerivative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem parametric_pullback_frame {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    (p : M) (γ : ℝ → M) (s : ℝ) (H : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hq : γ s ∈ (trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p).baseSet)
    (hH : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' V z.2 (H z.1 z.2)) (s, γ s))
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p
    deriv (fun t ↦ H t (γ s)) s + D.connection (H s) (γ s) (curveVelocity γ s) =
      ∑ i, (e.localFrameCoeff (𝓡 n) b i (γ s) (H s (γ s)) •
        D.connection (e.localFrame b i) (γ s) (curveVelocity γ s) +
        deriv (fun t ↦ e.localFrameCoeff (𝓡 n) b i (γ t) (H t (γ t))) s •
          e.localFrame b i (γ s)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) p
  have hspatial : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (H s)) (γ s) :=
    hH.comp (γ s) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have htime := parametric_frame_time_derivative g b p (γ s) s H hq hH
  have hconn := connection_localFrame D b p (γ s) hq (H s) hspatial (curveVelocity γ s)
  dsimp only at htime hconn ⊢
  rw [htime.deriv, hconn, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hchain := hasDerivAt_parametric_curve
    (fun z : ℝ × M ↦ e.localFrameCoeff (𝓡 n) b i z.2 (H z.1 z.2)) γ s
    (mdifferentiableAt_parametric_frameCoeff b p (γ s) s H hq hH i) hγ
  change _ = e.localFrameCoeff (𝓡 n) b i (γ s) (H s (γ s)) •
      D.connection (e.localFrame b i) (γ s) (curveVelocity γ s) +
      deriv (fun t ↦ e.localFrameCoeff (𝓡 n) b i (γ t) (H t (γ t))) s •
        e.localFrame b i (γ s)
  rw [hchain.deriv, add_smul]
  abel

end PoincareConjecture.Proofs.M09
