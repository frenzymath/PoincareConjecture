import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteChartDifferential





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem chart_affine_metric (g : RiemannianMetric n M) (p : M)
    (e : ℂ ≃L[ℝ] E) (a : E)
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {f : E → M} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f (a + e z))
    (hs : f (a + e z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hg : gE.euclideanCoefficients ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z))) =
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z)))) (v w : ℂ) :
    gE.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z)))
        (fderiv ℝ (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e y))) z v)
        (fderiv ℝ (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e y))) z w) =
      g.inner (f (a + e z)) (mfderiv 𝓘(ℝ, E) (𝓡 n) f (a + e z) (e v))
        (mfderiv 𝓘(ℝ, E) (𝓡 n) f (a + e z) (e w)) := by
  simpa +instances only [fderivWithin_univ, mfderivWithin_univ] using!
    within_chart_affine_metric g p e a hf.mdifferentiableWithinAt
      (uniqueDiffWithinAt_univ (x := z))
      (show MapsTo (fun y => a + e y) univ univ from fun _ _ => mem_univ _) hs hg v w

end PoincareConjecture.M64
