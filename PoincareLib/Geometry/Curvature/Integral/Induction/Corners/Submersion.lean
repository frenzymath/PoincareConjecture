import PoincareLib.Geometry.Curvature.Integral.Induction.Corners.Regularity
import PoincareLib.Geometry.Manifold.Submersion.FiniteDimensional

/-!
# Submersion charts for smooth corner strainers

The opposite and cross-gradient inequalities in Petrunin's Definition 3.1
give actual smooth submersion charts for the combined defining map. The
opposite vectors are arbitrary tangent vectors; smooth partner functions
are not assumed. Reference: author manuscript p. 5.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type*} [Fintype ι]

/-- A smooth family satisfying the corner strainer inequalities is a smooth
submersion to the finite Pi space. Joint surjectivity is derived from the
gradient inequalities, and the submersion is the actual chart normal form. -/
theorem strainer_isSubmersionAt
    (g : RiemannianMetric n M) (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i)) (x : M)
    (w : ι → TangentSpace (𝓡 n) x)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hsmall : (Fintype.card ι : ℝ) * δ < (1 - 2 * δ) ^ 2)
    (hh : ∀ i, g.tangentNorm x (w i) ≤ 1)
    (hopposite : ∀ i, g.inner x (g.gradient (f i) x) (w i) ≤ -1 + 2 * δ)
    (hcross : ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ) :
    Manifold.IsSubmersionAt (𝓡 n) 𝓘(ℝ, ι → ℝ) ∞ (fun y i => f i y) x := by
  apply Poincare.Geometry.Manifold.isSubmersionAt_of_surjective_mfderiv
    (contMDiff_pi_space.mpr hf) x
  have hsurj := (g.strainer_gradients_regular f x w hδ hδhalf hsmall
    hh hopposite hcross).2
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨v, ?_⟩
  funext i
  rw [Poincare.Geometry.Manifold.mfderiv_pi_apply f hf x v i]
  exact congrFun hv i

end PoincareMT.RiemannianMetric
