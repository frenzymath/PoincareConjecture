import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Coordinates.SimultaneousMarkedFormulas
import PoincareConjecture.Proofs.M76.Wall.Mathlib.CompatibleChartFormula

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_shared_marked_chart_refinement
    {E V X ι κ μ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [Finite κ] [Finite μ]
    {e : ι → OpenPartialHomeomorph X V} {f : E → X}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    (hJK : ∀ i, (J i).space ⊆ K.space)
    (B : κ → OpenPartialHomeomorph X V)
    (hcompat : ∀ j i, (e i).symm.trans (B j) ∈ piecewiseAffineGroupoid V)
    (hsource : ∀ i, MapsTo f (J i).space (B i).source)
    (P : μ → SimplicialComplex ℝ E) (hP : ∀ j, (P j).faces.Finite)
    (hPK : ∀ j, (P j).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E)
      (Q : μ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ i, L i ≤ R ∧ (L i).space = (J i).space ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L i).vertices) → s ∈ (L i).faces) ∧
        (L i).AffineOnFaces (B i ∘ f)) ∧
      ∀ j, Q j ≤ R ∧ (Q j).space = (P j).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (Q j).vertices) → s ∈ (Q j).faces := by
  have hcoords (i : κ) : FinitePiecewiseAffineOn (B i ∘ f) (J i).space :=
    hf.finitePiecewiseAffineOn_compatible_chart (B i) (hcompat i) (J i) (hJ i)
      (hJK i) (hsource i)
  exact K.exists_simultaneous_marked_formulas hK J hJ hJK
    (fun i => B i ∘ f) hcoords P hP hPK

end Geometry
