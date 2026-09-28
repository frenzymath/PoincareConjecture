import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Stokes.Chart

set_option autoImplicit false

open VectorField
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

structure AlignedChartFrame (g : RiemannianMetric 2 S)
    (e : OpenPartialHomeomorph S (ℝ × ℝ)) where
  first : (x : S) → TangentSpace (𝓡 2) x
  second : (x : S) → TangentSpace (𝓡 2) x
  smooth_first : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% first) e.source
  smooth_second : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% second) e.source
  unit_first : ∀ x ∈ e.source, g.inner x (first x) (first x) = 1
  unit_second : ∀ x ∈ e.source, g.inner x (second x) (second x) = 1
  orthogonal : ∀ x ∈ e.source, g.inner x (first x) (second x) = 0
  positive : ∀ x ∈ e.source,
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1)) x
    0 < g.inner x X (first x) * g.inner x Y (second x) -
      g.inner x X (second x) * g.inner x Y (first x)
  aligned : ∀ x ∈ e.source,
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x
    first x = (Real.sqrt (g.inner x X X))⁻¹ • X

noncomputable def alignedChartFrame (g : RiemannianMetric 2 S)
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target) :
    AlignedChartFrame g e := Classical.choice (by
  obtain ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp, ha⟩ :=
    LeviCivitaData.exists_aligned_positive_chart_frame g e he hei
  exact ⟨⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp, fun x _ => congrFun ha x⟩⟩)

end PoincareConjecture.RiemannianMetric
