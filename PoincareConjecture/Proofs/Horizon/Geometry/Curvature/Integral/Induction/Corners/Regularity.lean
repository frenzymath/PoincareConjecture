import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.GradientFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient

set_option autoImplicit false

open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type*} [Fintype ι]

theorem strainer_gradients_regular
    (g : RiemannianMetric n M) (f : ι → M → ℝ) (x : M)
    (w : ι → TangentSpace (𝓡 n) x)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hsmall : (Fintype.card ι : ℝ) * δ < (1 - 2 * δ) ^ 2)
    (hh : ∀ i, g.tangentNorm x (w i) ≤ 1)
    (hopposite : ∀ i, g.inner x (g.gradient (f i) x) (w i) ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ) :
    LinearIndependent ℝ (fun i => g.gradient (f i) x) ∧
      Function.Surjective (fun v : TangentSpace (𝓡 n) x => fun i =>
        mvfderiv (𝓡 n) (f i) x v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hv := Poincare.CurvatureIntegral.linearIndependent_of_strainer_pairs
    (fun i => g.gradient (f i) x) w
    hδ hδhalf hsmall hh hopposite hcross
  refine ⟨hv, ?_⟩
  have hs := Poincare.CurvatureIntegral.surjective_inner_family_of_linearIndependent hv
  convert hs using 1
  funext v i
  exact (g.inner_gradient (f i) x v).symm

theorem strainer_card_le_and_mfderiv_ne_zero
    (g : RiemannianMetric n M) (f : ι → M → ℝ) (x : M)
    (w : ι → TangentSpace (𝓡 n) x)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hsmall : (Fintype.card ι : ℝ) * δ < (1 - 2 * δ) ^ 2)
    (hh : ∀ i, g.tangentNorm x (w i) ≤ 1)
    (hopposite : ∀ i, g.inner x (g.gradient (f i) x) (w i) ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ) :
    Fintype.card ι ≤ n ∧ ∀ i, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f i) x ≠ 0 := by
  have hv := (g.strainer_gradients_regular f x w hδ hδhalf hsmall hh hopposite hcross).1
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  refine ⟨?_, fun i => ?_⟩
  · have hc := hv.fintype_card_le_finrank
    change Fintype.card ι ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) at hc
    simpa using hc
  · exact fun hi => hv.ne_zero i ((g.gradient_eq_zero_iff_mfderiv_eq_zero (f i) x).mpr hi)

end PoincareConjecture.RiemannianMetric
