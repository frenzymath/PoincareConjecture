import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Finite.ChartDifferential

/-! The ordinary metric identity in a genuine affine source chart.
This is the univ case of the checked within-domain chain rule.
Source: MT Lemma 19.15, pp. 447-449. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An ordinary affine coordinate change preserves the metric on the actual differential
columns wherever the target chart is valid. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
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

end PoincareMT.M64
