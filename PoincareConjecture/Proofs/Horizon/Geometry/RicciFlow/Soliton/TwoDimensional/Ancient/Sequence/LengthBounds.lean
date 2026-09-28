import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.ScalarBounds








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem backwardLIntegrand_nonneg (K : AncientKappaSolution 2 M)
    (γ : ℝ → M) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ backwardLIntegrand K.flow 0 γ s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨(K.flow.metric (0 - s)).toRiemannianMetric⟩
  apply mul_nonneg (Real.sqrt_nonneg s)
  exact add_nonneg ((K.flow.connection (0 - s)).scalar_nonnegative_of_nonnegative_curvatureOperator
    (γ s) (K.nonnegative_curvature_operator (0 - s) (by linarith) (γ s)))
    (show 0 ≤ inner ℝ (curveVelocity (n := 2) γ s) (curveVelocity (n := 2) γ s)
      from real_inner_self_nonneg)

theorem backwardLLength_nonneg (K : AncientKappaSolution 2 M)
    (γ : ℝ → M) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ backwardLLength K.flow 0 0 τ γ :=
  intervalIntegral.integral_nonneg hτ (fun _ hs => K.backwardLIntegrand_nonneg γ hs.1)

theorem reducedLength_nonneg (K : AncientKappaSolution 2 M)
    (p q : M) (τ : ℝ) : 0 ≤ reducedLength K.flow 0 p q τ := by
  unfold reducedLength
  split_ifs with hτ
  · apply div_nonneg _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg τ))
    apply Real.sInf_nonneg
    rintro L ⟨path, _, _, rfl⟩
    exact K.backwardLLength_nonneg path.curve hτ.le
  · exact le_rfl

theorem reducedLength_le_path (K : AncientKappaSolution 2 M)
    {p q : M} {τ : ℝ} (path : BackwardTimePath K.flow 0 0 τ)
    (hp : path.curve 0 = p) (hq : path.curve τ = q) :
    reducedLength K.flow 0 p q τ ≤ backwardLLength K.flow 0 0 τ path.curve /
      (2 * Real.sqrt τ) := by
  rw [reducedLength, dif_pos path.ordered]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg τ))
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro L ⟨γ, _, _, rfl⟩
    exact K.backwardLLength_nonneg γ.curve path.ordered.le
  · exact ⟨path, hp, hq, rfl⟩

end PoincareConjecture.AncientKappaSolution
